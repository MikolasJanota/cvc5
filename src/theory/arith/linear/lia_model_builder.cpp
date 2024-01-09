/*
 * File:  lia_model_builder.cpp
 * Author:  mikolas
 * Created on:  Wed Jun 7 09:53:23 CEST 2023
 * Copyright (C) 2023, Mikolas Janota
 */
#include "lia_model_builder.h"

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <iterator>  // ostream_iterator
#include <limits>
#include <numeric>  // for std::iota
#include <sstream>
#include <vector>

#include "expr/skolem_manager.h"
#include "options/arith_options.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory_model.h"
#include "theory/uf/theory_uf_model.h"

static inline double entr(size_t a, size_t b)
{
  if (!a || !b)
  {
    return 0;
  }
  const double t = a + b;
  const double ap = static_cast<double>(a) / t;
  const double bp = static_cast<double>(b) / t;
  return -ap * log(ap) - bp * log(bp);
}

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

/* == DEBUGGING == */

#define TRACELN1(prn)                                      \
  do                                                       \
  {                                                        \
    Trace("arith::lmb1") << "[lmb1] " << prn << std::endl; \
  } while (false);
#define TRACELN(prn)                                     \
  do                                                     \
  {                                                      \
    Trace("arith::lmb") << "[lmb] " << prn << std::endl; \
  } while (false);

static std::ostream& operator<<(std::ostream& os,
                                const LiaModelBuilder::FunArgs& args)
{
  os << "[";
  for (size_t i = 0; i < args.size(); i++)
  {
    os << (i ? " " : "") << args[i];
  }
  return os << "]";
}
static std::ostream& operator<<(std::ostream& os,
                                const LiaModelBuilder::FunPoint& p)
{
  return os << p.args << "->" << p.val;
}

static std::ostream& operator<<(
    std::ostream& os, const std::vector<LiaModelBuilder::FunPoint>& points)
{
  os << "[";
  size_t c = 0;
  for (const auto& a : points)
  {
    os << (c++ ? ", " : "") << a;
  }
  return os << "]";
}

static void dbg_trace_points(
    const std::vector<size_t>& indices,
    const std::vector<LiaModelBuilder::FunPoint>& points)
{
  if (TraceIsOn("arith::lmb1"))
  {
    TRACELN1("[");
    for (size_t i : indices)
    {
      TRACELN1(" " << points[i]);
    }
    TRACELN1("]");
  }
}

static void dbg_trace_points(
    size_t from, const std::vector<LiaModelBuilder::FunPoint>& points)
{
  if (TraceIsOn("arith::lmb1"))
  {
    TRACELN1("[");
    for (size_t i = from; i < points.size(); i++)
    {
      TRACELN1(" " << points[i]);
    }
    TRACELN1("]");
  }
}

inline bool getBool(TNode n)
{
  AlwaysAssert(n.getKind() == Kind::CONST_BOOLEAN);
  return n.getConst<bool>();
}

inline bool isNumeral(TNode n)
{
  return n.getKind() == Kind::CONST_INTEGER
         || n.getKind() == Kind::CONST_RATIONAL;
}

inline Rational getNumeral(TNode n)
{
  AlwaysAssert(isNumeral(n));
  return n.getConst<Rational>();
}

/** Lexicographic comparator of points. **/
struct LexPtCompare
{
  bool operator()(const LiaModelBuilder::FunPoint& a,
                  const LiaModelBuilder::FunPoint& b) const
  {
    const auto& aargs = a.args;
    const auto& bargs = b.args;
    Assert(aargs.size() == bargs.size());
    for (size_t i = 0; i < aargs.size(); i++)
    {
      if (aargs[i] != bargs[i])
      {
        return aargs[i] < bargs[i];
      }
    }
    Assert(a.val == b.val);
    return false;
  }
};

/* == CONSTRUCTION == */
LiaModelBuilder::LiaModelBuilder(Env& env, Node op, const std::string argPrefix)
    : EnvObj(env), d_op(op), d_argPrefix(argPrefix), d_typen(d_op.getType())
{
  NodeManager* const nm = NodeManager::currentNM();
  for (size_t i = 0; i + 1 < d_typen.getNumChildren(); i++)
  {
    std::stringstream ss;
    ss << d_argPrefix << (i + 1);
    d_vars.push_back(nm->mkBoundVar(ss.str(), d_typen[i]));
  }
}

void LiaModelBuilder::setValue(TheoryModel*, Node n, Node val, bool ground)
{
  Assert(ground) << "non-ground not supported";
  FunArgs args;
  args.reserve(n.getNumChildren());
  for (const Node& arg : n)
  {
    switch (arg.getKind())
    {
      case Kind::CONST_RATIONAL:
      case Kind::CONST_INTEGER: args.push_back(getNumeral(arg)); break;
      default:
        AlwaysAssert(false) << " expecting integers in the function points";
    }
  }
  AlwaysAssert(val.getKind() == Kind::CONST_INTEGER
               || val.getKind() == Kind::CONST_RATIONAL
               || val.getKind() == Kind::CONST_BOOLEAN)
      << "expecting reals/integers/bools in the function values";

  d_points.push_back({args, val});
}

/* == BUILDING MODEL == */
struct ExpressionHelper
{
  explicit ExpressionHelper(NodeManager* const nm, bool integers)
      : d_nm(nm),
        d_int(integers),
        d_tn(d_int ? nm->integerType() : nm->realType())
  {
  }

  NodeManager* const d_nm;
  const bool d_int;
  const TypeNode d_tn;

  inline Node mkNum(Rational val) { return d_nm->mkConstRealOrInt(d_tn, val); }
  inline Node mkZero() { return mkNum(Rational(0)); }

  Node mul(Rational a, TNode b)
  {
    if (a.isZero())
    {
      return mkZero();
    }
    if (a.isOne())
    {
      return b;
    }
    return d_nm->mkNode(Kind::MULT, mkNum(a), b);
  }

  inline bool isZero(TNode n)
  {
    return isNumeral(n) && n.getConst<Rational>().isZero();
  }

  /** Construct the sum of given terms. */
  inline Node sum(const std::vector<Node>& terms)
  {
    return terms.empty() ? mkZero()
                         : (terms.size() == 1 ? terms[0]
                                              : d_nm->mkNode(Kind::ADD, terms));
  }

  inline Node mul(TNode a, TNode b)
  {
    return isNumeral(a) ? mul(a.getConst<Rational>(), b)
                        : d_nm->mkNode(Kind::MULT, a, b);
  }

  /** Make polynomial from coeffs and vars, where the last coeff is the
   * intercept. */
  Node makePoly(const std::vector<Node>& coeffs, const std::vector<Node>& vars)
  {
    const auto arity = vars.size();
    Assert(arity + 1 == coeffs.size());
    std::vector<Node> terms;
    for (size_t i = 0; i < arity; i++)
    {
      if (!isZero(coeffs[i]))
      {
        terms.push_back(mul(coeffs[i], vars[i]));
      }
    }
    const Node& intercept = coeffs.back();
    if (!isZero(intercept))
    {
      terms.push_back(intercept);
    }
    return sum(terms);
  }

  Node makePredSegment(const std::vector<Node>& solution,
                       const std::vector<Node>& vars)
  {
    const Node fun = makePoly(solution, vars);
    return d_nm->mkNode(Kind::GEQ, fun, mkZero());
  }

  /** Create an inequality so that coefficients give a hyperplane fitting a
   * given point. */
  Node pt2ineq(const LiaModelBuilder::FunPoint& p,
               const std::vector<Node>& coefficients)
  {
    const auto arity = p.args.size();
    Assert(arity + 1 == coefficients.size());
    std::vector<Node> terms;
    for (size_t i = 0; i < arity; i++)
    {
      if (!p.args[i].isZero())
      {
        terms.push_back(mul(p.args[i], coefficients[i]));
      }
    }
    terms.push_back(coefficients[arity]);
    const Node rv = d_nm->mkNode(
        getBool(p.val) ? Kind::GEQ : Kind::LT, sum(terms), mkZero());
    TRACELN(p << " -> " << rv);
    return rv;
  }

  Node pt2eq(const LiaModelBuilder::FunPoint& p,
             const std::vector<Node>& coefficients)
  {
    const auto arity = p.args.size();
    Assert(arity + 1 == coefficients.size());
    std::vector<Node> terms;
    for (size_t i = 0; i < arity; i++)
    {
      if (!p.args[i].isZero())
      {
        terms.push_back(mul(p.args[i], coefficients[i]));
      }
    }
    terms.push_back(coefficients[arity]);
    const Node rv = sum(terms).eqNode(p.val);
    TRACELN(p << " -> " << rv);
    return rv;
  }

  std::vector<Node> mkCoefficients(const std::vector<Node>& vars)
  {
    std::vector<Node> coeffs;
    SkolemManager* const sm = d_nm->getSkolemManager();
    coeffs.reserve(vars.size() + 1);
    for (size_t i = 0; i < vars.size(); i++)
    {
      coeffs.push_back(sm->mkDummySkolem("k", d_tn, "coefficient in lmb"));
    }
    coeffs.push_back(sm->mkDummySkolem("c", d_tn, "intercept in lmb"));
    return coeffs;
  }
};

/** Copy solution from subsolver into coefficient values. **/
static void copySolution(std::unique_ptr<SolverEngine>& liaChecker,
                         const std::vector<Node>& coefficients,
                         std::vector<Node>& solution)
{
  solution.clear();
  for (const Node& n : coefficients)
  {
    solution.push_back(liaChecker->getValue(n));
  }
}

/** Pos/neg freq for predicates.
 *
 * Only points given by indices are considered. **/
static std::pair<size_t, size_t> freq(
    const std::vector<size_t>& indices,
    const std::vector<LiaModelBuilder::FunPoint>& points)
{
  size_t posCount = 0;
  size_t negCount = 0;
  for (size_t i : indices)
  {
    auto& counter = getBool(points[i].val) ? posCount : negCount;
    ++counter;
  }
  return {posCount, negCount};
}

static double calcGain(size_t posLeft,
                       size_t posCount,
                       size_t negLeft,
                       size_t negCount)
{
  Assert(posLeft <= posCount);
  Assert(negLeft <= negCount);
  const auto posRight = posCount - posLeft;
  const auto negRight = negCount - negLeft;
  const auto tot = static_cast<double>(posCount + negCount);
  const auto totLeft = static_cast<double>(posLeft + negLeft);
  const auto totRight = static_cast<double>(posRight + negRight);
  return -(totLeft / tot) * entr(posLeft, negLeft)
         - (totRight / tot) * entr(posRight, negRight);
}

static bool isPos(const LiaModelBuilder::FunArgs& args,
                  const std::vector<Node>& solution)
{
  const auto arity = args.size();
  Assert(arity + 1 == solution.size());
  Rational result;
  for (size_t i = 0; i < arity; i++)
  {
    auto v = getNumeral(solution[i]);
    v *= args[i];
    result += v;
  }
  result += getNumeral(solution[arity]);
  return result.sgn() >= 0;
}

/** Heuristically find a split index for given points at given indices. **/
static size_t findSplit(const std::vector<LiaModelBuilder::FunPoint>& points,
                        const std::vector<size_t>& indices,
                        size_t posCount,
                        size_t negCount)
{
  size_t posCountLeft = 0;
  size_t negCountLeft = 0;
  size_t split = -1;
  [[maybe_unused]] bool found = false;
  double maxGain = std::numeric_limits<double>::lowest();
  // find a pair of points with different value
  for (size_t ii = 0; ii + 1 < indices.size(); ii++)
  {
    const auto cur = points[indices[ii]];
    const auto next = points[indices[ii + 1]];
    auto& count = getBool(cur.val) ? posCountLeft : negCountLeft;
    ++count;
    if (cur.val == next.val)
    {
      continue;
    }
    // evaluate this split
    const auto gain = calcGain(posCountLeft, posCount, negCountLeft, negCount);
    if (gain > maxGain)
    {
      found = true;
      split = ii;
      maxGain = gain;
    }
  }
  Assert(found) << "there must be at least one splitting point";
  return split;
}

/** Run sat check on a given subsolver. **/
static inline bool checkSAT(std::unique_ptr<SolverEngine>& liaChecker)
{
  const Result r = liaChecker->checkSat();
  TRACELN("...got : " << r);
  switch (r.getStatus())
  {
    case Result::SAT: return true;
    case Result::UNSAT: return false;
    case Result::NONE:
    case Result::UNKNOWN:
      AlwaysAssert(false) << "failed on a QF_LIA in model construction";
  }
  Unreachable();
}

Node LiaModelBuilder::buildBodyFun() { return buildFunGreedyRec(0); }

Node LiaModelBuilder::buildBodyPred()
{
  return options().arith.lmbSmarterPred ? buildPredSmarter()
                                        : buildPredGreedyRec(0);
}

Node LiaModelBuilder::buildPredSmarter()
{
  std::vector<size_t> indices(d_points.size());
  std::iota(indices.begin(), indices.end(), 0);
  return buildPredSmarterRec(indices);
}

Node LiaModelBuilder::buildPredSmarterRec(const std::vector<size_t>& indices)
{
  Assert(!indices.empty());
  dbg_trace_points(indices, d_points);
  NodeManager* const nm = NodeManager::currentNM();
  const auto [posCount, negCount] = freq(indices, d_points);
  if (posCount == 0 || negCount == 0)
  {
    const auto rv = nm->mkConst<bool>(negCount == 0);
    TRACELN("const: " << rv);
    return rv;
  }

  const auto split = findSplit(d_points, indices, posCount, negCount);

  std::unique_ptr<SolverEngine> liaChecker;
  initializeSubsolver(liaChecker, d_env);
  liaChecker->setOption("produce-models", "true");
  liaChecker->setOption("incremental", "true");
  std::vector<Node> coefficients(d_h->mkCoefficients(d_vars));
  std::vector<Node> solution;
  TRACELN("splitting on: " << d_points[indices[split]] << ':'
                           << d_points[indices[split + 1]]);
  // first run on right off the split then left
  bool solvedAllRHS = true;
  bool solvedAllLHS = true;
  for (size_t ii = split; ii < indices.size() && solvedAllRHS; ++ii)
  {
    const auto point = d_points[indices[ii]];
    liaChecker->assertFormula(d_h->pt2ineq(point, coefficients));
    solvedAllRHS = checkSAT(liaChecker);
    if (solvedAllRHS)
    {
      copySolution(liaChecker, coefficients, solution);
      TRACELN("current sol: " << solution);
    }
  }
  if (solvedAllRHS)
  {
    TRACELN1("solvedAllRHS");
    for (size_t ii = split; ii-- && solvedAllLHS;)
    {
      const auto point = d_points[indices[ii]];
      liaChecker->assertFormula(d_h->pt2ineq(point, coefficients));
      solvedAllLHS = checkSAT(liaChecker);
      if (solvedAllLHS)
      {
        copySolution(liaChecker, coefficients, solution);
        TRACELN("current sol: " << solution);
      }
    }
  }
  Assert(isPos(d_points[indices[split]].args, solution)
         != isPos(d_points[indices[split + 1]].args, solution));
  const Node guard = d_h->makePredSegment(solution, d_vars);

  if (solvedAllRHS && solvedAllLHS)
  {
    TRACELN("sub-solution: " << guard);
    return guard;
  }

  // TODO: might be possible to reuse indices vector in the input
  // split points into positive and negative
  std::vector<size_t> posIndices;
  std::vector<size_t> negIndices;
  for (size_t i : indices)
  {
    auto& block = isPos(d_points[i].args, solution) ? posIndices : negIndices;
    block.push_back(i);
  }
  const Node posFun = buildPredSmarterRec(posIndices);
  const Node negFun = buildPredSmarterRec(negIndices);
  const Node rv = nm->mkNode(Kind::ITE, guard, posFun, negFun);
  TRACELN("sub-solution: " << rv);
  return rv;
}

Node LiaModelBuilder::buildPredGreedyRec(size_t ix)
{
  Assert(!d_points.empty());
  NodeManager* const nm = NodeManager::currentNM();
  const FunPoint& cur = d_points[ix];
  bool isConst = true;
  for (size_t i = ix + 1; i < d_points.size() && isConst; i++)
  {
    isConst = isConst && d_points[i].val == cur.val;
  }

  if (isConst)  // nothing to do, constant pred
  {
    return cur.val;
  }

  std::unique_ptr<SolverEngine> liaChecker;
  initializeSubsolver(liaChecker, d_env);
  liaChecker->setOption("produce-models", "true");
  liaChecker->setOption("incremental", "true");
  std::vector<Node> coefficients(d_h->mkCoefficients(d_vars));
  std::vector<Node> solution;
  for (; ix < d_points.size(); ix++)
  {
    liaChecker->assertFormula(d_h->pt2ineq(d_points[ix], coefficients));
    if (checkSAT(liaChecker))
    {
      copySolution(liaChecker, coefficients, solution);
      TRACELN("current sol: " << solution);
    }
    else
    {
      break;
    }
  }

  const Node firstSegment = solution.empty()
                                ? d_points[ix].val
                                : d_h->makePredSegment(solution, d_vars);
  if (ix >= d_points.size())  // all on single hyperplane
  {
    return firstSegment;
  }

  // create split
  const auto& lastCoor = d_points[ix - 1].args;
  const auto& splitCoor = d_points[ix].args;
  std::vector<Node> disjuncts;
  std::vector<Node> conj;
  size_t split_pos;
  for (split_pos = 0; split_pos < splitCoor.size()
                      && lastCoor[split_pos] == splitCoor[split_pos];
       split_pos++)
    ;
  if (split_pos < splitCoor.size())
  {
    split_pos++;
  }
  for (size_t i = 0; i < split_pos; i++)
  {
    const auto ci = d_h->mkNum(splitCoor[i]);
    conj.push_back(nm->mkNode(Kind::LT, d_vars[i], ci));
    disjuncts.push_back(nm->mkAnd(conj));
    conj.pop_back();
    if (i + 1 < split_pos)
    {
      conj.push_back(d_vars[i].eqNode(ci));
    }
  }
  return nm->mkNode(
      Kind::ITE, nm->mkOr(disjuncts), firstSegment, buildPredGreedyRec(ix));
}

Node LiaModelBuilder::buildFunGreedyRec(size_t ix)
{
  Assert(!d_points.empty());
  dbg_trace_points(ix, d_points);
  NodeManager* const nm = NodeManager::currentNM();
  const FunPoint& cur = d_points[ix++];
  if (ix >= d_points.size())  // nothing to do, single point
  {
    return cur.val;
  }
  std::unique_ptr<SolverEngine> liaChecker;
  initializeSubsolver(liaChecker, d_env);
  liaChecker->setOption("produce-models", "true");
  liaChecker->setOption("incremental", "true");
  std::vector<Node> coefficients(d_h->mkCoefficients(d_vars));
  // default solution is constant
  std::vector<Node> solution(coefficients.size(), d_h->mkZero());
  solution.back() = cur.val;
  TRACELN("cur: " << cur);
  TRACELN("coefficients: " << coefficients);
  TRACELN("current sol: " << solution);
  liaChecker->assertFormula(d_h->pt2eq(cur, coefficients));
  // greedily place points on a single hyperplane until impossible
  for (; ix < d_points.size(); ix++)
  {
    liaChecker->assertFormula(d_h->pt2eq(d_points[ix], coefficients));
    if (checkSAT(liaChecker))
    {
      copySolution(liaChecker, coefficients, solution);
      TRACELN("current sol: " << solution);
    }
    else
    {
      break;
    }
  }

  const Node firstSegment = d_h->makePoly(solution, d_vars);
  if (ix >= d_points.size())
  {
    return firstSegment;
  }

  // create a split expression
  const auto& lastCoor = d_points[ix - 1].args;
  const auto& splitCoor = d_points[ix].args;
  std::vector<Node> disjuncts;
  std::vector<Node> conj;
  size_t split_pos;
  for (split_pos = 0; split_pos < splitCoor.size()
                      && lastCoor[split_pos] == splitCoor[split_pos];
       split_pos++)
    ;
  if (split_pos < splitCoor.size())
  {
    split_pos++;
  }
  for (size_t i = 0; i < split_pos; i++)
  {
    const auto ci = d_h->mkNum(splitCoor[i]);
    conj.push_back(nm->mkNode(Kind::LT, d_vars[i], ci));
    disjuncts.push_back(nm->mkAnd(conj));
    conj.pop_back();
    if (i + 1 < split_pos)
    {
      conj.push_back(d_vars[i].eqNode(ci));
    }
  }
  return nm->mkNode(
      Kind::ITE, nm->mkOr(disjuncts), firstSegment, buildFunGreedyRec(ix));
}

/** Reduce repeated points */
void reduce(std::vector<LiaModelBuilder::FunPoint>& points)
{
  size_t j = 1;
  size_t lastIx = 0;
  for (size_t i = 1; i < points.size(); i++)
  {
    if (points[i].args == points[lastIx].args)
    {
      Assert(points[i].val == points[lastIx].val);
      continue;
    }
    if (j != i) points[j] = points[i];
    lastIx = j;
    ++j;
  }
  points.resize(j);
}

void LiaModelBuilder::simplify()
{
  if (d_points.empty())
  {
    return;
  }
  TRACELN("simplify for: " << d_op);
  TRACELN1("points: " << d_points);
  std::sort(d_points.begin(), d_points.end(), LexPtCompare());
  reduce(d_points);
  TRACELN1("reduced points: " << d_points);
  Assert(d_typen.getNumChildren() > 0);
  const auto arity = d_vars.size();
  const bool isPred = d_typen[arity].isBoolean();
  const bool isInt = arity > 0 && d_typen[0].isInteger();
  d_h.reset(new ExpressionHelper(NodeManager::currentNM(), isInt));
  d_body = isPred ? buildBodyPred() : buildBodyFun();
  TRACELN("simplified " << d_op << ": " << d_body);
}

/* == GETTERS == */

Node LiaModelBuilder::getFunctionValue(const std::string& argPrefix,
                                       Rewriter* r)
{
  Assert(d_argPrefix == argPrefix);
  NodeManager* const nm = NodeManager::currentNM();

  if (d_body.isNull())  // construct silly function, TODO: needed?
  {
    d_body = d_default;
    for (const auto& [args, v] : d_points)
    {
      Assert(args.size() == d_vars.size());
      std::vector<Node> eqs(args.size());
      for (size_t i = 0; i < args.size(); i++)
      {
        eqs[i] = d_vars[i].eqNode(d_h->mkNum(args[i]));
      }
      d_body = nm->mkNode(Kind::ITE, nm->mkAnd(eqs), v, d_body);
    }
  }

  if (r != nullptr)
  {
    d_body = r->rewrite(d_body);
  }

  const Node boundVarList = nm->mkNode(Kind::BOUND_VAR_LIST, d_vars);
  return nm->mkNode(Kind::LAMBDA, boundVarList, d_body);
}

LiaModelBuilder::~LiaModelBuilder() {}

bool LiaModelBuilder::canHandle(const Node op)
{
  const TypeNode tn = op.getType();
  const auto sz = tn.getNumChildren();
  Assert(sz > 0);
  const TypeNode& trv = tn[sz - 1];
  bool allInt = trv.isInteger() || trv.isBoolean();
  bool allReal = trv.isReal() || trv.isBoolean();
  for (size_t i = 0, iend = sz - 1; i < iend; i++)
  {
    allInt &= tn[i].isInteger();
    allReal &= tn[i].isReal();
    if (!allInt && !allReal)
    {
      return false;
    }
  }
  return true;
}

void LiaModelBuilder::debugPrint(std::ostream& out, TheoryModel* m, int ind)
{
  Assert(0);
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
