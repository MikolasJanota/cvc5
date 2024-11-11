/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for term enumeration.
 */

#include "theory/quantifiers/term_probgen.h"

#include <cstddef>
#include <vector>

#include "theory/quantifiers/quantifiers_state.h"

#define TRLN(CMD)                                    \
  do                                                 \
  {                                                  \
    Trace("probgen") << "[pg] " << CMD << std::endl; \
  } while (0);

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& o, const std::vector<Node>& vec)
{
  o << '[';
  for (size_t i = 0; i < vec.size(); ++i)
  {
    o << (i > 0 ? "," : "") << vec[i];
  }
  return o << ']';
}
namespace theory {
namespace quantifiers {

std::ostream& operator<<(std::ostream& o,
                         const std::vector<std::pair<Node, SymbolInfo>>& vec)
{
  {
    o << '[';
    for (size_t i = 0; i < vec.size(); ++i)
    {
      o << (i > 0 ? "," : "") << vec[i].first;
    }
    return o << ']';
  }
}

TermProbGen::TermProbGen(Env& env, QuantifiersState& qs)
    : QuantifiersUtil(env), d_qs(qs), d_rnde(977)
{
}

void TermProbGen::registerQuantifier(Node q)
{
  TRLN("registerQuantifier " << q);
  processFormula(q);
}

bool TermProbGen::reset(Theory::Effort e)
{
  d_ques.clear();
  d_qinfo.clear();
  d_symbols.clear();
  return true;
}

std::string TermProbGen::identify() const { return "TermProbGen"; }

void TermProbGen::clearQues() { d_ques.clear(); }

void TermProbGen::getTermsForType(TypeNode tn, std::vector<Node>& terms)
{
  auto [it, isNew] = d_ques.insert({tn, std::vector<Node>()});
  auto& que = it->second;
  if (isNew)
  {
    fillQue(tn, que);
  }
  terms.insert(terms.end(), que.begin(), que.end());
}

const SymbolInfo SymbolInfo::s_one(1);

Node TermProbGen::pick(const std::vector<std::pair<Node, SymbolInfo>>& vec)
{
  if (vec.empty())
  {
    return Node::null();
  }
  std::uniform_real_distribution<> dist(0.0, 1.0);
  for (const auto& rec : vec)
  {
    if (dist(d_rnde) < 0.4)
    {
      return rec.first;
    }
  }
  return vec.begin()->first;
}

Node TermProbGen::makeNode(TypeNode range_tn, size_t depth)
{
  TRLN("Genereting node for " << range_tn);
  const auto rv = makeNodeInternal(range_tn, depth);
  TRLN("Genereted node " << rv);
  return rv;
}

Node TermProbGen::makeNodeInternal(TypeNode range_tn, size_t depth)
{
  TRLN("makeNodeInternal " << range_tn << '@' << depth);
  const auto& vecs = d_symbols.d_vecs;
  const auto& it = vecs.find(range_tn);
  if (it == vecs.end())
  {
    return Node::null();
  }
  const auto s = pick(it->second);
  TRLN("picked symbol " << s << " out of " << it->second);
  if (s.isNull())
  {
    return Node::null();
  }
  const auto tn = s.getType();
  TRLN("type " << tn << " " << s.getKind() << ":" << s.getMetaKind());
  if (s.getMetaKind() == kind::MetaKind::CONSTANT
      || s.getMetaKind() == kind::MetaKind::VARIABLE)
  {
    return s;
  }
  Assert(s.getKind() != Kind::APPLY_UF);
  if (s.getKind() != Kind::APPLY_UF)
  {
    return Node::null();
  }

  /* Assert(tn.getRangeType() == range_tn); */
  const bool parametrized = tn.getMetaKind() == kind::MetaKind::PARAMETERIZED;
  std::vector<Node> args;
  if (parametrized)
  {
    args.push_back(s);
  }
  for (size_t i = 0; i < args.size(); ++i)
  {
    const auto nn = makeNode(tn[i], depth + 1);
    if (nn.isNull())
    {
      return Node::null();
    }
    args.push_back(nn);
  }
  auto* const nm = d_env.getNodeManager();
  return nm->mkNode(parametrized ? Kind::APPLY_UF : s.getKind(), args);
}

size_t TermProbGen::fillQue(TypeNode tn, /*out*/ std::vector<Node>& que)
{
  TRLN("fillQue:" << tn);
  size_t count;
  for (count = 0; count < 20; count++)
  {
    if (const Node t = makeNode(tn); !t.isNull())
    {
      que.push_back(t);
    }
    else
    {
      break;
    }
  };
  return count;
}

void TermProbGen::addSymbol(Node n)
{
  const Node& symbol = n.hasOperator() ? n.getOperator() : n;
  const TypeNode tn = symbol.getType();
  const TypeNode rtn = tn.isFunctionLike() ? tn.getRangeType() : tn;
  auto& tm = d_symbols.d_maps[rtn];
  const auto [it, isNew] = tm.insert({symbol, SymbolInfo::s_one});
  if (!isNew)  // existing symbol, just increase
  {
    it->second.d_count++;
  }
  TRLN("addSymbol:" << n << "->" << symbol << "->" << rtn << "->" << it->first
                    << ":" << it->second.d_count);
}

void TermProbGen::processFormula(Node t)
{
  TRLN("processFormula:" << t);
  std::set<Node> seen;
  TNode cur;
  std::vector<Node> stack = {t};
  do
  {
    cur = stack.back();
    stack.pop_back();
    if (seen.insert(cur).second)
    {
      if (cur.getKind() == Kind::APPLY_UF
          || cur.getMetaKind() == kind::MetaKind::CONSTANT
          || cur.getMetaKind() == kind::MetaKind::VARIABLE)
      {
        addSymbol(cur);
      }
      stack.insert(stack.end(), cur.begin(), cur.end());
    }
  } while (!stack.empty());
}

void TermProbGen::processInstantiation(Node q,
                                       const std::vector<Node>& terms,
                                       bool success)
{
  Assert(q.getKind() == Kind::FORALL);
  if (!success)
  {
    return;
  }
  TRLN("processInstantiation:" << q << ":" << terms);
  d_symbols.d_vecs.clear();
  for (const Node& t : terms)
  {
    processFormula(t);
  }
  for (const auto& [tn, m] : d_symbols.d_maps)
  {
    auto& vec = d_symbols.d_vecs[tn];
    for (const auto& [s, si] : m)
    {
      vec.push_back({s, si});
    }
    using T = std::pair<Node, SymbolInfo>;
    std::sort(vec.begin(), vec.end(), [](T const& a, T const& b) -> bool {
      return a.second.d_count > b.second.d_count;
    });
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
