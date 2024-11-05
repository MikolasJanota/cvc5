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
 * Pool-based instantiation strategy
 */

#include "theory/quantifiers/inst_strategy_probgen.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/term_probgen.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_tuple_enumerator.h"

using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstStrategyProbGen::InstStrategyProbGen(Env& env,
                                         QuantifiersState& qs,
                                         QuantifiersInferenceManager& qim,
                                         QuantifiersRegistry& qr,
                                         TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr)
{
}

void InstStrategyProbGen::presolve() {}

bool InstStrategyProbGen::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}

void InstStrategyProbGen::reset_round(Theory::Effort e) {}

void InstStrategyProbGen::check(Theory::Effort e, QEffort quant_e)
{
  beginCallDebug();
  FirstOrderModel* const fm = d_treg.getModel();
  const size_t nquant = fm->getNumAssertedQuantifiers();
  bool inConflict = false;
  uint64_t addedLemmas = 0;
  for (size_t i = 0; !inConflict && i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i, true);
    inConflict = process(q, addedLemmas);
  }
  endCallDebug();
}

std::string InstStrategyProbGen::identify() const { return "probgen-inst"; }

bool InstStrategyProbGen::process(Node q, uint64_t& addedLemmas)
{
  // otherwise, process standard
  Instantiate* ie = d_qim.getInstantiate();
  TermTupleEnumeratorEnv ttec;
  ttec.d_fullEffort = true;
  ttec.d_increaseSum = options().quantifiers.enumInstSum;
  ttec.d_tr = &d_treg;
  std::shared_ptr<TermTupleEnumeratorInterface> enumerator(
      mkTermTupleEnumeratorProbGen(q, &ttec));
  std::vector<Node> terms;
  std::vector<bool> failMask;
  for (enumerator->init(); enumerator->hasNext();)
  {
    if (d_qstate.isInConflict())
    {
      // could be conflicting for an internal reason
      return true;
    }
    enumerator->next(terms);
    // try instantiation
    failMask.clear();
    if (ie->addInstantiationExpFail(
            q, terms, failMask, InferenceId::QUANTIFIERS_INST_POOL))  // TODO
    {
      Trace("inst-alg-pt") << "Success with " << terms << std::endl;
      addedLemmas++;
    }
    else
    {
      Trace("inst-alg-pt") << "Fail with " << terms << std::endl;
      // notify the enumerator of the failure
      enumerator->failureReason(failMask);
    }
  }
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
