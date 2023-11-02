#include "theory/origin_tracker.h"

#include "base/map_util.h"
using namespace cvc5::internal::kind;

/* == DEBUGGING == */
#define TRACELN(prn)                              \
  do                                              \
  {                                               \
    Trace("ogt") << "[ogt] " << prn << std::endl; \
  } while (false);
#define TRACELN1(prn)                               \
  do                                                \
  {                                                 \
    Trace("ogt1") << "[ogt1] " << prn << std::endl; \
  } while (false);

static const char* toStr(cvc5::internal::theory::OriginTracker::OriginType ot)
{
  using OT = cvc5::internal::theory::OriginTracker::OriginType;
  switch (ot)
  {
    case OT::Lemma: return "LEM";
    case OT::Sk: return "SK";
    case OT::SkAssert: return "SKA";
    case OT::InputAssert: return "IN";
  }
  return nullptr;
}
/* == End of DEBUGGING == */

namespace cvc5::internal {
namespace theory {

OriginTracker::OriginTracker(Env& env, TheoryEngine* engine)
    : TheoryEngineModule(env, engine, "OriginTracker")
{
}

void OriginTracker::check(Theory::Effort effort) {}
void OriginTracker::postCheck(Theory::Effort effort) {}

void OriginTracker::notifyLemma(TNode n,
                                theory::LemmaProperty p,
                                const std::vector<Node>& skAsserts,
                                const std::vector<Node>& sks)
{
  TRACELN("notifyLemma: " << n);
  assignSubterms(n, {n, OriginType::Lemma});
  for (const Node& s : sks)
  {
    assignSubterms(s, {n, OriginType::Sk});
  }
  for (const Node& s : skAsserts)
  {
    assignSubterms(s, {n, OriginType::SkAssert});
  }
}

void OriginTracker::notifyPreprocessedAssertions(
    const std::vector<Node>& assertions)
{
  for (const Node& n : assertions)
  {
    assignSubterms(n, {n, OriginType::InputAssert});
  }
}

void OriginTracker::assignTerm(TNode n, const Origin& s)
{
  d_origins[n] = s;
  TRACELN1(toStr(s.d_type) << ": " << n << " <-- " << s.d_lemma);
}

void OriginTracker::assignSubterms(TNode n, const Origin& s)
{
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    const auto [_, inserted] = d_seen.insert(cur);
    if (!inserted)
    {
      continue;
    }
    if (cur.isClosure())
    {
      assignTerm(cur, s);
      continue;
    }
    visit.insert(visit.end(), cur.begin(), cur.end());
    if (!cur.getType().isBoolean())
    {
      assignTerm(cur, s);
    }
  } while (!visit.empty());
}

}  // namespace theory
}  // namespace cvc5::internal
