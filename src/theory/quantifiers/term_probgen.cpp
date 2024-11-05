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
namespace theory {
namespace quantifiers {

TermProbGen::TermProbGen(Env& env, QuantifiersState& qs)
    : QuantifiersUtil(env), d_qs(qs), d_rnde(977)
{
}

void TermProbGen::registerQuantifier(Node q) {}

std::string TermProbGen::identify() const { return "TermProbGen"; }

void TermProbGen::getTermsForType(TypeNode tn, std::vector<Node>& terms)
{
  const auto it = d_ques.find(tn);
  if (it != d_ques.end())
  {
    terms.insert(terms.end(), it->second.begin(), it->second.end());
  }
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

Node TermProbGen::makeNode(TypeNode range_tn)
{
  const auto& vecs = d_symbols.d_vecs;
  const auto& it = vecs.find(range_tn);
  if (it == vecs.end())
  {
    return Node::null();
  }
  const auto s = pick(it->second);
  if (s.isNull())
  {
    return Node::null();
  }
  const auto tn = s.getType();
  Assert(tn.getRangeType() == range_tn);
  std::vector<Node> args(tn.getNumChildren());
  for (size_t i = 0; i < args.size(); ++i)
  {
    args[i] = makeNode(tn[i]);
    if (args[i].isNull())
    {
      return Node::null();
    }
  }
  switch (s.getMetaKind())
  {
    case kind::MetaKind::OPERATOR:
      /**< operators that get "inlined" */
      break;
    case kind::MetaKind::PARAMETERIZED:
      /**< parameterized ops (like APPLYs) that carry extra data */
      break;
    case kind::MetaKind::CONSTANT:
      /**< constants */
      break;
    default: Unhandled() << "unexpected meta kind" << s.getMetaKind();
  }

  return Node::null();
}

size_t TermProbGen::fillQue(TypeNode tn, /*out*/ std::vector<Node>& que)
{
  size_t count;
  for (count = 0; count < 20; count++)
  {
    const Node t = makeNode(tn);
    if (t.isNull())
    {
      break;
    }
    que.push_back(t);
  };
  return count;
}

void TermProbGen::addSymbol(Node n)
{
  const Node& symbol = n.hasOperator() ? n.getOperator() : n;
  const TypeNode tn = symbol.getType();
  const TypeNode rtn = tn.getRangeType();
  auto& tm = d_symbols.d_maps[tn];
  const auto [it, added] = tm.insert({symbol, SymbolInfo::s_one});
  if (!added)
  {
    it->second.d_count++;
  }
  TRLN("sym" << it->first << ":" << tn << ":" << it->second.d_count);
}

void TermProbGen::processTerm(Node t)
{
  std::set<Node> seen;
  TNode cur;
  std::vector<Node> stack = {t};
  do
  {
    cur = stack.back();
    stack.pop_back();
    if (seen.insert(cur).second)
    {
      addSymbol(cur);
      stack.insert(stack.end(), cur.begin(), cur.end());
    }
  } while (!stack.empty());
}

void TermProbGen::processInstantiation(Node q,
                                       const std::vector<Node>& terms,
                                       bool success)
{
  Assert(q.getKind() == Kind::FORALL);
  d_symbols.d_vecs.clear();
  if (success)
  {
    for (const Node& t : terms)
    {
      processTerm(t);
    }
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
