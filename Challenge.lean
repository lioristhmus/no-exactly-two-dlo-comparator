import Mathlib

/-!
# Trusted statement for the exact-two Diderot Comparator

This file deliberately does **not** import the proof repository.  It repeats
only the definitions that occur transitively in the public endpoint

`Provable Zsep (∼ spec2Sentence)`.

The definitions have the same fully qualified names and bodies as the pinned
formalization.  Comparator checks that the independently compiled Solution
uses exactly these declarations.  The single `sorry` at the end is the trusted
challenge hole required by the Comparator protocol; it is not presented as a
proof.
-/

namespace ExactThreeDLO
namespace FO

open FirstOrder Language BoundedFormula

/-! ## The first-order language of set theory -/

inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

protected def Lmem : Language := ⟨fun _ => Empty, memRel⟩

def memF {α : Type} {n : ℕ} (t₁ t₂ : (FO.Lmem).Term (α ⊕ (Fin n))) :
    (FO.Lmem).BoundedFormula α n :=
  Relations.boundedFormula₂ (memRel.mem) t₁ t₂

/-! ## The object theory `Zsep` -/

def extAx : (FO.Lmem).Sentence :=
  ∀' ∀' ((∀' (memF &2 &0 ⇔ memF &2 &1)) ⟹ (&0 =' &1))

def pairAx : (FO.Lmem).Sentence :=
  ∀' ∀' ∃' ∀' (memF &3 &2 ⇔ ((&3 =' &0) ⊔ (&3 =' &1)))

def unionAx : (FO.Lmem).Sentence :=
  ∀' ∃' ∀' (memF &2 &1 ⇔ ∃' (memF &3 &0 ⊓ memF &2 &3))

def powerAx : (FO.Lmem).Sentence :=
  ∀' ∃' ∀' (memF &2 &1 ⇔ ∀' (memF &3 &2 ⟹ memF &3 &0))

def infAx : (FO.Lmem).Sentence :=
  ∃' ((∃' (memF &1 &0 ⊓ ∀' (∼ (memF &2 &1)))) ⊓
    ∀' (memF &1 &0 ⟹ ∃' (memF &2 &0 ⊓
      ∀' (memF &3 &2 ⇔ (memF &3 &1 ⊔ (&3 =' &1))))))

def sepAx {n : ℕ} (φ : (FO.Lmem).BoundedFormula Empty (n + 1)) : (FO.Lmem).Sentence :=
  (∀' ∃' ∀' ((memF &(⟨n + 2, by omega⟩ : Fin (n + 1 + 1 + 1))
      &(⟨n + 1, by omega⟩ : Fin (n + 1 + 1 + 1))) ⇔
    ((memF &(⟨n + 2, by omega⟩ : Fin (n + 1 + 1 + 1))
        &(⟨n, by omega⟩ : Fin (n + 1 + 1 + 1))) ⊓
      (φ.liftAt 2 n)))).alls

def Zsep : (FO.Lmem).Theory :=
  {extAx, pairAx, unionAx, powerAx, infAx} ∪
    (Set.range fun p : (Σ n : ℕ, (FO.Lmem).BoundedFormula Empty (n + 1)) => sepAx p.2)

/-! ## Named free variables and the derivation calculus -/

def bv0 {n : ℕ} (j : ℕ) : Fin (n + 1) → ℕ ⊕ Fin n :=
  Fin.cons (Sum.inl j) (fun s => Sum.inr s)

@[simp]
def sub0 : ∀ {n : ℕ}, ℕ → (FO.Lmem).BoundedFormula ℕ (n + 1) →
    (FO.Lmem).BoundedFormula ℕ n
  | _, _, .falsum => .falsum
  | _, j, .equal t₁ t₂ =>
      .equal (t₁.relabel (Sum.elim Sum.inl (bv0 j))) (t₂.relabel (Sum.elim Sum.inl (bv0 j)))
  | _, j, .rel R ts => .rel R (fun i => (ts i).relabel (Sum.elim Sum.inl (bv0 j)))
  | _, j, .imp φ ψ => .imp (sub0 j φ) (sub0 j ψ)
  | _, j, .all φ => .all (sub0 j φ)

@[simp]
def ofSentAux : ∀ {n : ℕ}, (FO.Lmem).BoundedFormula Empty n →
    (FO.Lmem).BoundedFormula ℕ n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ =>
      .equal (t₁.relabel (Sum.map Empty.elim id)) (t₂.relabel (Sum.map Empty.elim id))
  | _, .rel R ts => .rel R (fun i => (ts i).relabel (Sum.map Empty.elim id))
  | _, .imp φ ψ => .imp (ofSentAux φ) (ofSentAux ψ)
  | _, .all φ => .all (ofSentAux φ)

def ofSent (σ : (FO.Lmem).Sentence) : (FO.Lmem).Formula ℕ := ofSentAux σ

def vEq (i j : ℕ) : (FO.Lmem).Formula ℕ :=
  (var (Sum.inl i)) =' (var (Sum.inl j))

def vMem (i j : ℕ) : (FO.Lmem).Formula ℕ :=
  memF (var (Sum.inl i)) (var (Sum.inl j))

inductive Deriv : Set ((FO.Lmem).Formula ℕ) → (FO.Lmem).Formula ℕ → Type
  | hyp {Γ : Set ((FO.Lmem).Formula ℕ)} {φ} : φ ∈ Γ → Deriv Γ φ
  | weak {Γ Γ' : Set ((FO.Lmem).Formula ℕ)} {φ} : Γ ⊆ Γ' → Deriv Γ φ → Deriv Γ' φ
  | impI {Γ} {φ ψ} : Deriv (insert φ Γ) ψ → Deriv Γ (φ ⟹ ψ)
  | impE {Γ} {φ ψ} : Deriv Γ (φ ⟹ ψ) → Deriv Γ φ → Deriv Γ ψ
  | raa {Γ} {φ} : Deriv (insert (∼ φ) Γ) ⊥ → Deriv Γ φ
  | allI {Γ} {ψ : (FO.Lmem).BoundedFormula ℕ 1} (i : ℕ) :
      i ∉ ψ.freeVarFinset → (∀ γ ∈ Γ, i ∉ γ.freeVarFinset) →
      Deriv Γ (sub0 i ψ) → Deriv Γ ψ.all
  | allE {Γ} {ψ : (FO.Lmem).BoundedFormula ℕ 1} (j : ℕ) :
      Deriv Γ ψ.all → Deriv Γ (sub0 j ψ)
  | eqRefl {Γ} (i : ℕ) : Deriv Γ (vEq i i)
  | eqMemL {Γ} (i j k : ℕ) : Deriv Γ (vEq i j ⟹ (vMem i k ⟹ vMem j k))
  | eqMemR {Γ} (i j k : ℕ) : Deriv Γ (vEq i j ⟹ (vMem k i ⟹ vMem k j))
  | eqEqL {Γ} (i j k : ℕ) : Deriv Γ (vEq i j ⟹ (vEq i k ⟹ vEq j k))
  | eqEqR {Γ} (i j k : ℕ) : Deriv Γ (vEq i j ⟹ (vEq k i ⟹ vEq k j))

def theoryHyp (T : (FO.Lmem).Theory) : Set ((FO.Lmem).Formula ℕ) := ofSent '' T

abbrev Provable (T : (FO.Lmem).Theory) (σ : (FO.Lmem).Sentence) : Type :=
  Deriv (theoryHyp T) (ofSent σ)

/-! ## Formula constructors used by the exact-two sentence -/

def lastSplit (n : ℕ) : Fin (n + 1) → Fin n ⊕ Fin 1 := fun i =>
  if h : (i : ℕ) < n then Sum.inl ⟨i, h⟩ else Sum.inr 0

def fMem {n : ℕ} (i j : Fin n) : (FO.Lmem).Formula (Fin n) :=
  memF (var (Sum.inl i)) (var (Sum.inl j))

def fEq {n : ℕ} (i j : Fin n) : (FO.Lmem).Formula (Fin n) :=
  (var (Sum.inl i)) =' (var (Sum.inl j))

def fAnd {n : ℕ} (ψ χ : (FO.Lmem).Formula (Fin n)) :
    (FO.Lmem).Formula (Fin n) := ψ ⊓ χ

def fNot {n : ℕ} (ψ : (FO.Lmem).Formula (Fin n)) :
    (FO.Lmem).Formula (Fin n) := ∼ ψ

def fOr {n : ℕ} (ψ χ : (FO.Lmem).Formula (Fin n)) :
    (FO.Lmem).Formula (Fin n) := ψ ⊔ χ

def fImp {n : ℕ} (ψ χ : (FO.Lmem).Formula (Fin n)) :
    (FO.Lmem).Formula (Fin n) := ψ ⟹ χ

def fIff {n : ℕ} (ψ χ : (FO.Lmem).Formula (Fin n)) :
    (FO.Lmem).Formula (Fin n) := ψ ⇔ χ

def fComp {n m : ℕ} (ψ : (FO.Lmem).Formula (Fin n)) (σ : Fin n → Fin m) :
    (FO.Lmem).Formula (Fin m) := ψ.relabel σ

noncomputable def fAll {n : ℕ} (ψ : (FO.Lmem).Formula (Fin (n + 1))) :
    (FO.Lmem).Formula (Fin n) :=
  Formula.iAlls (Fin 1) (ψ.relabel (lastSplit n))

noncomputable def fEx {n : ℕ} (ψ : (FO.Lmem).Formula (Fin (n + 1))) :
    (FO.Lmem).Formula (Fin n) :=
  fNot (fAll (fNot ψ))

def fClose (ψ : (FO.Lmem).Formula (Fin 0)) : (FO.Lmem).Sentence :=
  ψ.relabel (fun i => Fin.elim0 i)

/-! ## The sentence asserting an exact-three same-carrier DLO spectrum -/

noncomputable def fEqOpair : (FO.Lmem).Formula (Fin 3) :=
  fAll (fIff (fMem 3 2)
    (fOr (fAll (fIff (fMem 4 3) (fEq 4 0)))
      (fAll (fIff (fMem 4 3) (fOr (fEq 4 0) (fEq 4 1))))))

noncomputable def fOpairMem : (FO.Lmem).Formula (Fin 3) :=
  fEx (fAnd (fComp fEqOpair ![0, 1, 3]) (fMem 3 2))

noncomputable def fLt : (FO.Lmem).Formula (Fin 3) :=
  fComp fOpairMem ![1, 2, 0]

noncomputable def fMemProd : (FO.Lmem).Formula (Fin 3) :=
  fEx (fAnd (fMem 3 0) (fEx (fAnd (fMem 4 1) (fComp fEqOpair ![3, 4, 2]))))

noncomputable def fEqApp : (FO.Lmem).Formula (Fin 3) :=
  fAll (fIff (fMem 3 2) (fEx (fAnd (fComp fOpairMem ![1, 4, 0]) (fMem 3 4))))

noncomputable def fIsFunc : (FO.Lmem).Formula (Fin 3) :=
  fAnd (fAll (fImp (fMem 3 0) (fComp fMemProd ![1, 2, 3])))
    (fAnd (fAll (fAll (fAll (fImp (fComp fOpairMem ![3, 4, 0])
        (fImp (fComp fOpairMem ![3, 5, 0]) (fEq 4 5))))))
      (fAll (fImp (fMem 3 1) (fEx (fComp fOpairMem ![3, 4, 0])))))

noncomputable def fIsInj : (FO.Lmem).Formula (Fin 1) :=
  fAll (fAll (fAll (fImp (fComp fOpairMem ![1, 3, 0])
    (fImp (fComp fOpairMem ![2, 3, 0]) (fEq 1 2)))))

noncomputable def fIsOnto : (FO.Lmem).Formula (Fin 2) :=
  fAll (fImp (fMem 2 1) (fEx (fComp fOpairMem ![3, 2, 0])))

noncomputable def fIsSLO : (FO.Lmem).Formula (Fin 2) :=
  fAnd (fAll (fImp (fMem 2 0)
      (fEx (fAnd (fMem 3 1) (fEx (fAnd (fMem 4 1) (fComp fEqOpair ![3, 4, 2])))))))
    (fAnd (fAll (fNot (fComp fLt ![0, 2, 2])))
      (fAnd (fAll (fAll (fAll (fImp (fComp fLt ![0, 2, 3])
            (fImp (fComp fLt ![0, 3, 4]) (fComp fLt ![0, 2, 4]))))))
        (fAll (fAll (fImp (fMem 2 1) (fImp (fMem 3 1)
          (fOr (fComp fLt ![0, 2, 3])
            (fOr (fEq 2 3) (fComp fLt ![0, 3, 2])))))))))

noncomputable def fDense : (FO.Lmem).Formula (Fin 2) :=
  fAll (fAll (fImp (fMem 2 1) (fImp (fMem 3 1) (fImp (fComp fLt ![0, 2, 3])
    (fEx (fAnd (fMem 4 1) (fAnd (fComp fLt ![0, 2, 4]) (fComp fLt ![0, 4, 3]))))))))

noncomputable def fNoLeast : (FO.Lmem).Formula (Fin 2) :=
  fAll (fImp (fMem 2 1) (fEx (fAnd (fMem 3 1) (fComp fLt ![0, 3, 2]))))

noncomputable def fNoGreatest : (FO.Lmem).Formula (Fin 2) :=
  fAll (fImp (fMem 2 1) (fEx (fAnd (fMem 3 1) (fComp fLt ![0, 2, 3]))))

noncomputable def fIsDLO : (FO.Lmem).Formula (Fin 2) :=
  fAnd fIsSLO (fAnd (fEx (fMem 2 1)) (fAnd fDense (fAnd fNoLeast fNoGreatest)))

noncomputable def fOrdClause : (FO.Lmem).Formula (Fin 5) :=
  fAll (fAll (fImp (fMem 5 2) (fImp (fMem 6 2) (fIff (fComp fLt ![1, 5, 6])
    (fEx (fAnd (fComp fEqApp ![0, 5, 7])
      (fEx (fAnd (fComp fEqApp ![0, 6, 8]) (fComp fLt ![3, 7, 8])))))))))

noncomputable def fIsOrderIso : (FO.Lmem).Formula (Fin 5) :=
  fAnd (fComp fIsFunc ![0, 2, 4])
    (fAnd (fComp fIsInj ![0]) (fAnd (fComp fIsOnto ![0, 4]) fOrdClause))

noncomputable def fOrderIsom : (FO.Lmem).Formula (Fin 4) :=
  fEx (fComp fIsOrderIso ![4, 0, 1, 2, 3])

noncomputable def fPairIso : (FO.Lmem).Formula (Fin 3) :=
  fComp fOrderIsom ![1, 0, 2, 0]

noncomputable def fSpec3Body : (FO.Lmem).Formula (Fin 4) :=
  fAnd (fComp fIsDLO ![1, 0])
    (fAnd (fComp fIsDLO ![2, 0])
    (fAnd (fComp fIsDLO ![3, 0])
    (fAnd (fNot (fComp fPairIso ![0, 1, 2]))
    (fAnd (fNot (fComp fPairIso ![0, 2, 1]))
    (fAnd (fNot (fComp fPairIso ![0, 1, 3]))
    (fAnd (fNot (fComp fPairIso ![0, 3, 1]))
    (fAnd (fNot (fComp fPairIso ![0, 2, 3]))
    (fNot (fComp fPairIso ![0, 3, 2])))))))))

noncomputable def fSpecGe3 : (FO.Lmem).Formula (Fin 1) :=
  fEx (fEx (fEx fSpec3Body))

end FO
end ExactThreeDLO

namespace ExactTwoDLO
namespace FO

open ExactThreeDLO ExactThreeDLO.FO

/-! ## The sentence asserting an exact-two same-carrier DLO spectrum -/

-- `![...]` synthesizes this private finite-index witness in the standalone
-- `NoExactlyTwoDlo.FO.Spec2` module.  The Challenge is one Mathlib-only module,
-- so the elaborator would otherwise reuse an earlier private witness from the
-- copied exact-three surface.  Naming the same proof explicitly and supplying
-- it to each `Fin 3` numeral preserves the exported constant graph exactly.
theorem fSpec2Body._proof_1 :
    @NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) (2 + 1) :=
  @Nat.instNeZeroSucc 2
attribute [local instance] fSpec2Body._proof_1

noncomputable def fSpec2Body : (ExactThreeDLO.FO.Lmem).Formula (Fin 3) :=
  fAnd (fComp fIsDLO ![1, 0])
    (fAnd (fComp fIsDLO ![2, 0])
    (fAnd (fNot (fComp fPairIso ![0, 1, 2]))
    (fNot (fComp fPairIso ![0, 2, 1]))))

noncomputable def fSpecGe2 : (ExactThreeDLO.FO.Lmem).Formula (Fin 1) :=
  fEx (fEx fSpec2Body)

noncomputable def fSpecEq2 : (ExactThreeDLO.FO.Lmem).Formula (Fin 1) :=
  fAnd fSpecGe2 (fNot fSpecGe3)

noncomputable def spec2Sentence : (ExactThreeDLO.FO.Lmem).Sentence :=
  fClose (fEx fSpecEq2)

end FO
end ExactTwoDLO

open FirstOrder Language BoundedFormula

namespace ExactTwoDLO.Comparator

/-- Trusted theorem hole.  `Provable` is Type-valued, so `Nonempty` exposes
existence of the exact derivation object as a proposition that Comparator 4.29
can compare, axiom-audit, and replay in the kernel. -/
theorem derivable :
    Nonempty (ExactThreeDLO.FO.Provable ExactThreeDLO.FO.Zsep (∼ FO.spec2Sentence)) :=
  by sorry

end ExactTwoDLO.Comparator
