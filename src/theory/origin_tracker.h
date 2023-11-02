#include "cvc5_private.h"

#ifndef CVC5__THEORY__ORIGIN_TRACKER__H
#define CVC5__THEORY__ORIGIN_TRACKER__H

#include <optional>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "expr/term_context.h"
#include "theory/theory_engine_module.h"

namespace cvc5::internal {
namespace theory {

class TheoryModel;

/**
 */
class OriginTracker : public TheoryEngineModule
{
 public:
  enum OriginType
  {
    Lemma,
    Sk,
    SkAssert,
    InputAssert
  };
  struct Origin
  {
    Node d_lemma;
    OriginType d_type;
    InferenceId d_infId;
    LemmaProperty d_lemProp;
    static Origin mkIn(TNode n)
    {
      return {
          n, OriginType::InputAssert, InferenceId::NONE, LemmaProperty::NONE};
    }
    static Origin mkLem(OriginType ot,
                        TNode n,
                        InferenceId infId,
                        LemmaProperty lemProp)
    {
      return {n, ot, infId, lemProp};
    }
  };

 public:
  /**
   * @param env The environment
   * @param engine The parent theory engine
   */
  OriginTracker(Env& env, TheoryEngine* engine);
  virtual ~OriginTracker() {}
  /**
   * Begin round, called at the beginning of a full effort check in
   * TheoryEngine.
   */
  void check(Theory::Effort effort) override;
  /** End round, called at the end of a full effort check in TheoryEngine. */
  void postCheck(Theory::Effort effort) override;

  /** Notify lemma, for difficulty measurements */
  void notifyLemma(TNode n,
                   InferenceId id,
                   LemmaProperty p,
                   const std::vector<Node>& skAsserts,
                   const std::vector<Node>& sks) override;

  /** Needs candidate model, return true if the method below requires calling */
  bool needsCandidateModel() override { return false; }

  const std::unordered_map<Node, Origin>& origins() const { return d_origins; }

  std::optional<Origin> getOrigin(Node n) const
  {
    const auto it = d_origins.find(n);
    return it == d_origins.end() ? std::nullopt
                                 : std::optional<Origin>{it->second};
  }

  /**
   */
  void notifyPreprocessedAssertions(const std::vector<Node>& assertions);

 private:
  std::unordered_set<Node> d_seen;
  std::unordered_map<Node, Origin> d_origins;
  void assignSubterms(TNode n, const Origin& s);
  void assignSubterms(const std::vector<Node>& ns, const Origin& s)
  {
    for (const auto& n : ns)
    {
      assignSubterms(n, s);
    }
  }
  void assignTerm(TNode n, const Origin& s);
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ORIGIN_TRACKER__H */
