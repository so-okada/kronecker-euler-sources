import KroneckerPeriodicWords

/-! The two buffers, two partial periods and equal periodic collars close exactly. -/
set_option autoImplicit false
namespace KroneckerPeriodicCapIdentity
open KroneckerPeriodicWords

theorem cap_identity (u v : ℕ) (T : List ℕ) (t j : ℕ) :
    repeatRuns (u::(T++[v])) j ++
      (u::((T++[v])++repeatRuns (u::(T++[v])) t++[u]++T)++[v]) ++
      repeatRuns (u::(T++[v])) j = repeatRuns (u::(T++[v])) (t+2+2*j) := by
  let W := u::(T++[v])
  have hmiddle : u::((T++[v])++repeatRuns W t++[u]++T)++[v] = repeatRuns W (t+2) := by
    have h := repeatRuns_sandwich W t 0
    simpa [W,repeatRuns,List.cons_append,List.append_assoc] using h
  change repeatRuns W j ++ (u::((T++[v])++repeatRuns W t++[u]++T)++[v]) ++
    repeatRuns W j = repeatRuns W (t+2+2*j)
  rw [hmiddle,←repeatRuns_add,←repeatRuns_add]
  congr 1
  omega

end KroneckerPeriodicCapIdentity
