import Tests.PartACanonicalAuditSupport

/-! Infrastructure regression: the first audit must not freeze the environment
before the named declarations below. No original Part A proof is changed. -/
#print axioms True.intro
#partA_axioms "True.intro"

namespace PartACanonical.Audit.CacheRegression

def lateIdentity (n : Nat) : Nat := n
theorem lateIdentity_eq (n : Nat) : lateIdentity n = n := rfl
theorem lateIdentity_eq_full (n : Nat) : lateIdentity n = n := lateIdentity_eq n

def check_lateIdentity : Nat → Nat := lateIdentity
def check_lateIdentity_eq : ∀ (n : Nat), lateIdentity n = n := lateIdentity_eq
def check_lateIdentity_eq_full : ∀ (n : Nat), lateIdentity n = n := lateIdentity_eq_full

private def privateValue : Nat := 7
def check_privateValue : Nat := privateValue
def «7» : Nat := 7
def check_quotedSeven : Nat := «7»
def «with.dot» : Nat := 3
def check_quotedDot : Nat := «with.dot»

#check (check_lateIdentity : Nat → Nat)
#check (check_lateIdentity_eq : ∀ (n : Nat), lateIdentity n = n)
#check (check_lateIdentity_eq_full : ∀ (n : Nat), lateIdentity n = n)
#check (privateValue : Nat)
#check (check_privateValue : Nat)
#check (check_quotedSeven : Nat)
#check (check_quotedDot : Nat)

#print axioms lateIdentity
#print axioms lateIdentity_eq
#print axioms lateIdentity_eq_full
#print axioms check_lateIdentity
#print axioms check_lateIdentity_eq
#print axioms check_lateIdentity_eq_full
#print axioms privateValue
#print axioms check_privateValue
#print axioms «7»
#print axioms check_quotedSeven
#print axioms «with.dot»
#print axioms check_quotedDot

#partA_axioms "PartACanonical.Audit.CacheRegression.lateIdentity"
#partA_axioms "PartACanonical.Audit.CacheRegression.lateIdentity_eq"
#partA_axioms "PartACanonical.Audit.CacheRegression.lateIdentity_eq_full"
#partA_axioms "PartACanonical.Audit.CacheRegression.check_lateIdentity"
#partA_axioms "PartACanonical.Audit.CacheRegression.check_lateIdentity_eq"
#partA_axioms "PartACanonical.Audit.CacheRegression.check_lateIdentity_eq_full"
#partA_axioms "_private.Tests.PartACanonicalAuditCacheTests.0.PartACanonical.Audit.CacheRegression.privateValue"
#partA_axioms "PartACanonical.Audit.CacheRegression.check_privateValue"
#partA_axioms "PartACanonical.Audit.CacheRegression.«7»"
#partA_axioms "PartACanonical.Audit.CacheRegression.check_quotedSeven"
#partA_axioms "PartACanonical.Audit.CacheRegression.«with.dot»"
#partA_axioms "PartACanonical.Audit.CacheRegression.check_quotedDot"

end PartACanonical.Audit.CacheRegression
