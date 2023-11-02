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
std::ostream& operator<<(std::ostream& out, OriginTracker::OriginType ot)
{
  return out << toStr(ot);
}

std::ostream& operator<<(std::ostream& out, const OriginTracker::Origin& o)
{
  if (o.d_type == OriginTracker::OriginType::InputAssert)
  {
    return out << o.d_type << ":" << o.d_lemma;
  }
  return out << o.d_type << ":" << o.d_lemma << "," << o.d_infId << ","
             << o.d_lemProp;
}

OriginTracker::OriginTracker(Env& env, TheoryEngine* engine)
    : TheoryEngineModule(env, engine, "OriginTracker"),
      d_newTermIdStats(statisticsRegistry().registerHistogram<InferenceId>(
          "inferencesOrigins"))
{
}

void OriginTracker::check(Theory::Effort effort) {}
void OriginTracker::postCheck(Theory::Effort effort) {}

void OriginTracker::notifyLemma(TNode n,
                                InferenceId id,
                                LemmaProperty p,
                                const std::vector<Node>& skAsserts,
                                const std::vector<Node>& sks)
{
  TRACELN("notifyLemma: " << n);
  assignSubterms(n, Origin::mkLem(OriginType::Lemma, n, id, p));
  assignSubterms(sks, Origin::mkLem(OriginType::Sk, n, id, p));
  assignSubterms(skAsserts, Origin::mkLem(OriginType::SkAssert, n, id, p));
}

void OriginTracker::notifyPreprocessedAssertions(
    const std::vector<Node>& assertions)
{
  for (const auto& n : assertions)
  {
    assignSubterms(n, Origin::mkIn(n));
  }
}

void OriginTracker::assignTerm(TNode n, const Origin& s)
{
  if (s.d_type != OriginType::InputAssert)
  {
    d_newTermIdStats << s.d_infId;
  }
  d_origins[n] = s;
  TRACELN1("assgn: " << n << " <-- " << s);
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
