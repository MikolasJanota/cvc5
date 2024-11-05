/******************************************************************************
 * Top contributors (to current version):
 *   Mikolas Janota
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

#include <random>

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__TERM_PROBGEN_H
#define CVC5__THEORY__QUANTIFIERS__TERM_PROBGEN_H

#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "theory/quantifiers/quant_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersState;

/**
 *
 * TODO
 */
struct SymbolInfo
{
  u_int64_t d_count;
  constexpr explicit SymbolInfo(u_int64_t count) : d_count(count) {}
  const static SymbolInfo s_one;
};

/**
 *
 * TODO
 */
class TermProbQuantInfo
{
 public:
  /** initialize, which clears the data below */
  void initialize();
};

template <class T>
struct SymbolsInfo
{
  std::map<TypeNode, std::map<T, SymbolInfo>> d_maps;
  std::map<TypeNode, std::vector<std::pair<T, SymbolInfo>>> d_vecs;
  void init_vecs();
};

/**
 * TODO
 */
class TermProbGen : public QuantifiersUtil
{
 public:
  TermProbGen(Env& env, QuantifiersState& qs);
  virtual ~TermProbGen() {}
  /** reset, which resets the current values of TODO */
  bool reset(Theory::Effort e) override;
  /** TODO */
  void registerQuantifier(Node q) override;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const override;
  /**
   * Process instantiation, called at the moment we successfully instantiate
   * q with terms.*/
  void processInstantiation(Node q,
                            const std::vector<Node>& terms,
                            bool success);

  void getTermsForType(TypeNode p, std::vector<Node>& terms);

 private:
  /** reference to the quantifiers state */
  QuantifiersState& d_qs;
  /** Maps types to a domain */
  std::map<TypeNode, std::vector<Node>> d_ques;
  /** Maps quantifiers to info */
  std::map<Node, TermProbQuantInfo> d_qinfo;

  SymbolsInfo<Node> d_symbols;

  std::mt19937 d_rnde;

  void processTerm(Node t);
  void addSymbol(Node t);
  size_t fillQue(TypeNode tn, /*out*/ std::vector<Node>& que);
  Node makeNode(TypeNode tn);
  Node pick(const std::vector<std::pair<Node, SymbolInfo>>& vec);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
