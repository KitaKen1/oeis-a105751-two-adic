import Mathlib

/-!
# OEIS A105751: the 2-adic asymptotic

This standalone, mathlib-only file proves the exact target registered in Formal Conjectures.
It first proves exact valuations in all four residue classes and then derives the limit.
-/

open Complex Filter Topology Nat

namespace A105751Proof

/-- The pair `(r,s)` represents the Gaussian integer `r + 4 s i`. -/
structure Quad4 where
  re : ℤ
  im : ℤ
deriving DecidableEq

namespace Quad4

@[ext] theorem ext {x y : Quad4} (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x
  cases y
  simp_all

def one : Quad4 := ⟨1, 0⟩

def mul (z w : Quad4) : Quad4 :=
  ⟨z.re * w.re - 16 * z.im * w.im, z.re * w.im + z.im * w.re⟩

@[simp] theorem one_re : one.re = 1 := rfl
@[simp] theorem one_im : one.im = 0 := rfl
@[simp] theorem mul_re (z w : Quad4) : (mul z w).re = z.re * w.re - 16 * z.im * w.im := rfl
@[simp] theorem mul_im (z w : Quad4) : (mul z w).im = z.re * w.im + z.im * w.re := rfl

theorem mul_assoc (x y z : Quad4) : mul (mul x y) z = mul x (mul y z) := by
  ext <;> simp [mul] <;> ring

theorem mul_comm (x y : Quad4) : mul x y = mul y x := by
  ext <;> simp [mul] <;> ring

@[simp] theorem one_mul (x : Quad4) : mul one x = x := by
  ext <;> simp [mul]

@[simp] theorem mul_one (x : Quad4) : mul x one = x := by
  rw [mul_comm, one_mul]

/-- The determinant comparing the two formal slopes `im / re`. -/
def cross (z w : Quad4) : ℤ := z.im * w.re - z.re * w.im

def norm4 (z : Quad4) : ℤ := z.re ^ 2 + 16 * z.im ^ 2

theorem cross_mul_right (x y z : Quad4) :
    cross (mul x z) (mul y z) = norm4 z * cross x y := by
  simp [cross, norm4, mul]
  ring

theorem cross_mul_left (x y z : Quad4) :
    cross (mul z x) (mul z y) = norm4 z * cross x y := by
  simpa [mul_comm] using cross_mul_right x y z

theorem cross_trans_num (x y z : Quad4) :
    y.re * cross x z = z.re * cross x y + x.re * cross y z := by
  simp [cross]
  ring

theorem odd_re_mul {x y : Quad4} (hx : Odd x.re) (hy : Odd y.re) :
    Odd (mul x y).re := by
  rcases hx with ⟨a, ha⟩
  rcases hy with ⟨b, hb⟩
  refine ⟨2 * a * b + a + b - 8 * x.im * y.im, ?_⟩
  simp only [mul_re, ha, hb]
  ring

/-- Product of `len` consecutive factors, beginning at `start`. -/
def prodFrom (f : ℕ → Quad4) (start : ℕ) : ℕ → Quad4
  | 0 => one
  | len + 1 => mul (prodFrom f start len) (f (start + len))

@[simp] theorem prodFrom_zero (f : ℕ → Quad4) (start : ℕ) :
    prodFrom f start 0 = one := rfl

@[simp] theorem prodFrom_succ (f : ℕ → Quad4) (start len : ℕ) :
    prodFrom f start (len + 1) = mul (prodFrom f start len) (f (start + len)) := rfl

theorem prodFrom_add (f : ℕ → Quad4) (start a b : ℕ) :
    prodFrom f start (a + b) =
      mul (prodFrom f start a) (prodFrom f (start + a) b) := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Nat.add_succ, prodFrom_succ, ih, prodFrom_succ]
      rw [mul_assoc]
      congr 2
      simp [Nat.add_assoc]

theorem odd_re_prodFrom (f : ℕ → Quad4) (hf : ∀ n, Odd (f n).re)
    (start len : ℕ) : Odd (prodFrom f start len).re := by
  induction len with
  | zero => exact odd_one
  | succ len ih => exact odd_re_mul ih (hf _)

end Quad4

/-- `ExactTwo k z` means that the exact power of two dividing `z` is `2^k`. -/
def ExactTwo (k : ℕ) (z : ℤ) : Prop :=
  ∃ u : ℤ, Odd u ∧ z = (2 : ℤ) ^ k * u

theorem exactTwo_zero_iff_odd (z : ℤ) : ExactTwo 0 z ↔ Odd z := by
  simp [ExactTwo]

theorem ExactTwo.nonzero {k : ℕ} {z : ℤ} (h : ExactTwo k z) : z ≠ 0 := by
  rcases h with ⟨u, hu, rfl⟩
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by
    intro huz
    subst u
    norm_num at hu)

theorem ExactTwo.mul_odd {k : ℕ} {z u : ℤ} (hz : ExactTwo k z) (hu : Odd u) :
    ExactTwo k (z * u) := by
  rcases hz with ⟨v, hv, rfl⟩
  refine ⟨v * u, hv.mul hu, ?_⟩
  ring

theorem ExactTwo.neg {k : ℕ} {z : ℤ} (hz : ExactTwo k z) : ExactTwo k (-z) := by
  rcases hz with ⟨u, hu, rfl⟩
  refine ⟨-u, hu.neg, ?_⟩
  ring

theorem pow_two_dvd_of_dvd_mul_odd (k : ℕ) {r z : ℤ} (hr : Odd r)
    (h : (2 : ℤ) ^ k ∣ r * z) : (2 : ℤ) ^ k ∣ z := by
  have hcop : IsCoprime (2 : ℤ) r := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hr.natAbs.coprime_two_left
  exact hcop.pow_left.dvd_of_dvd_mul_left h

theorem ExactTwo.of_mul_odd {k : ℕ} {z u : ℤ} (hzu : ExactTwo k (z * u))
    (hu : Odd u) : ExactTwo k z := by
  rcases hzu with ⟨v, hv, hvEq⟩
  have hd : (2 : ℤ) ^ k ∣ z * u := ⟨v, hvEq⟩
  have hdz : (2 : ℤ) ^ k ∣ z := by
    rw [mul_comm] at hd
    exact pow_two_dvd_of_dvd_mul_odd k hu hd
  rcases hdz with ⟨w, hw⟩
  refine ⟨w, ?_, hw⟩
  have hwumul : Odd (w * u) := by
    rw [hw] at hvEq
    have heq : w * u = v := by
      apply mul_left_cancel₀ (pow_ne_zero k (by norm_num : (2 : ℤ) ≠ 0))
      simpa [mul_assoc] using hvEq
    exact heq ▸ hv
  exact (Int.odd_mul.mp hwumul).1

theorem Quad4.cross_prodFrom_dvd
    (f g : ℕ → Quad4) (hf : ∀ n, Odd (f n).re) (hg : ∀ n, Odd (g n).re)
    (startF startG len N : ℕ)
    (hcross : ∀ j < len, (2 : ℤ) ^ N ∣ Quad4.cross (f (startF + j)) (g (startG + j))) :
    (2 : ℤ) ^ N ∣
      Quad4.cross (Quad4.prodFrom f startF len) (Quad4.prodFrom g startG len) := by
  induction len with
  | zero => simp [Quad4.prodFrom, Quad4.cross]
  | succ len ih =>
      let p := Quad4.prodFrom f startF len
      let q := Quad4.prodFrom g startG len
      let a := f (startF + len)
      let b := g (startG + len)
      let x := Quad4.mul p a
      let y := Quad4.mul q a
      let z := Quad4.mul q b
      have hpq : (2 : ℤ) ^ N ∣ Quad4.cross p q :=
        ih (fun j hj ↦ hcross j (Nat.lt_succ_of_lt hj))
      have hab : (2 : ℤ) ^ N ∣ Quad4.cross a b := by
        exact hcross len (Nat.lt_succ_self len)
      have hxy : (2 : ℤ) ^ N ∣ Quad4.cross x y := by
        rw [show Quad4.cross x y = Quad4.norm4 a * Quad4.cross p q by
          exact Quad4.cross_mul_right p q a]
        exact dvd_mul_of_dvd_right hpq _
      have hyz : (2 : ℤ) ^ N ∣ Quad4.cross y z := by
        rw [show Quad4.cross y z = Quad4.norm4 q * Quad4.cross a b by
          exact Quad4.cross_mul_left a b q]
        exact dvd_mul_of_dvd_right hab _
      have hyre : Odd y.re :=
        Quad4.odd_re_mul (Quad4.odd_re_prodFrom g hg startG len) (hf _)
      have hmul : (2 : ℤ) ^ N ∣ y.re * Quad4.cross x z := by
        rw [Quad4.cross_trans_num x y z]
        exact dvd_add (dvd_mul_of_dvd_right hxy _) (dvd_mul_of_dvd_right hyz _)
      have hxz : (2 : ℤ) ^ N ∣ Quad4.cross x z :=
        pow_two_dvd_of_dvd_mul_odd N hyre hmul
      simpa [x, z, p, q, a, b, Quad4.prodFrom_succ] using hxz

theorem exactTwo_mul_im_of_cross {k : ℕ} {p q : Quad4}
    (hpim : ExactTwo k p.im) (hqim : ExactTwo k q.im)
    (hqre : Odd q.re)
    (hcross : (2 : ℤ) ^ (k + 2) ∣ Quad4.cross p q) :
    ExactTwo (k + 1) (Quad4.mul p q).im := by
  rcases hpim with ⟨u, hu, hpu⟩
  rcases hqim with ⟨v, hv, hqv⟩
  rcases hcross with ⟨c, hc⟩
  refine ⟨u * q.re - 2 * c, (hu.mul hqre).sub_even ⟨c, by ring⟩, ?_⟩
  simp only [Quad4.mul_im, hpu, hqv, Quad4.cross] at hc ⊢
  simp only [pow_succ] at hc ⊢
  ring_nf at hc ⊢
  omega

/-- A dyadic block of factors has exactly the expected power of two in its
normalized imaginary coordinate. -/
theorem exactTwo_prodFrom_pow
    (f : ℕ → Quad4) (hre : ∀ n, Odd (f n).re) (him : ∀ n, Odd (f n).im)
    (hshift : ∀ x d : ℕ,
      (4 : ℤ) * d ∣ Quad4.cross (f x) (f (x + d)))
    (start k : ℕ) :
    ExactTwo k (Quad4.prodFrom f start (2 ^ k)).im := by
  induction k generalizing start with
  | zero =>
      simpa [Quad4.prodFrom, exactTwo_zero_iff_odd] using him start
  | succ k ih =>
      let L : ℕ := 2 ^ k
      let p := Quad4.prodFrom f start L
      let q := Quad4.prodFrom f (start + L) L
      have hpim : ExactTwo k p.im := ih start
      have hqim : ExactTwo k q.im := ih (start + L)
      have hqre : Odd q.re := Quad4.odd_re_prodFrom f hre (start + L) L
      have hpq : (2 : ℤ) ^ (k + 2) ∣ Quad4.cross p q := by
        apply Quad4.cross_prodFrom_dvd f f hre hre start (start + L) L (k + 2)
        intro j hj
        have h := hshift (start + j) L
        have hidx : start + L + j = start + j + L := by omega
        rw [hidx]
        convert h using 1
        simp [L, pow_add]
        ring
      have hmul : ExactTwo (k + 1) (Quad4.mul p q).im :=
        exactTwo_mul_im_of_cross hpim hqim hqre hpq
      have hsplit : 2 ^ (k + 1) = L + L := by
        simp [L, pow_succ]
        omega
      rw [hsplit, Quad4.prodFrom_add]
      simpa [p, q] using hmul

/-- The normalized imaginary coordinate of a product of equally-scaled factors
has the parity of the number of factors. -/
theorem scaledParity_prodFrom
    (g : ℕ → Quad4) (hre : ∀ n, Odd (g n).re)
    {k : ℕ} (him : ∀ n, ExactTwo k (g n).im)
    (start len : ℕ) :
    ∃ u : ℤ,
      (Quad4.prodFrom g start len).im = (2 : ℤ) ^ k * u ∧
      (Odd u ↔ Odd (len : ℤ)) := by
  induction len with
  | zero =>
      refine ⟨0, by simp [Quad4.prodFrom], ?_⟩
      norm_num
  | succ len ih =>
      rcases ih with ⟨u, hu, hpar⟩
      rcases him (start + len) with ⟨v, hv, hvEq⟩
      let p := Quad4.prodFrom g start len
      let a := g (start + len)
      refine ⟨p.re * v + u * a.re, ?_, ?_⟩
      · simp only [Quad4.prodFrom_succ, Quad4.mul_im, hu, hvEq, p, a]
        ring
      · have hpodd : Odd p.re := Quad4.odd_re_prodFrom g hre start len
        have haodd : Odd a.re := hre _
        have hfirst : Odd (p.re * v) := hpodd.mul hv
        have hsecond : Odd (u * a.re) ↔ Odd u := by
          simp [Int.odd_mul, haodd]
        have hlen : Odd ((len + 1 : ℕ) : ℤ) ↔ ¬ Odd (len : ℤ) := by
          simp only [Nat.cast_add, Nat.cast_one, Int.odd_add]
          simp
        rw [Int.odd_add, hlen]
        have hsecondEven : Even (u * a.re) ↔ ¬ Odd u := by
          rw [← Int.not_odd_iff_even, Int.odd_mul]
          simp [haodd]
        rw [hsecondEven]
        simpa [hfirst] using not_congr hpar

/-- Exact two-adic order for an arbitrary nonempty initial block. -/
theorem exactTwo_prodFrom
    (f : ℕ → Quad4) (hre : ∀ n, Odd (f n).re) (him : ∀ n, Odd (f n).im)
    (hshift : ∀ x d : ℕ,
      (4 : ℤ) * d ∣ Quad4.cross (f x) (f (x + d)))
    (start len : ℕ) (hlen : len ≠ 0) :
    ExactTwo (padicValNat 2 len) (Quad4.prodFrom f start len).im := by
  let k := padicValNat 2 len
  let L := 2 ^ k
  let blocks := len / L
  have hLdvd : L ∣ len := by
    simpa [L, k] using (pow_padicValNat_dvd (p := 2) (n := len))
  have hlen_eq : blocks * L = len := by
    exact Nat.div_mul_cancel hLdvd
  have hblocks_ne : blocks ≠ 0 := by
    intro hb
    rw [hb, zero_mul] at hlen_eq
    exact hlen hlen_eq.symm
  have hblocks_odd : Odd blocks := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro htwo
    rcases htwo with ⟨c, hc⟩
    have hbad : 2 ^ (k + 1) ∣ len := by
      refine ⟨c, ?_⟩
      rw [← hlen_eq, hc]
      simp [L, pow_succ]
      ring
    exact pow_succ_padicValNat_not_dvd (p := 2) hlen hbad
  let g : ℕ → Quad4 := fun j ↦ Quad4.prodFrom f (start + j * L) L
  have gre : ∀ j, Odd (g j).re := by
    intro j
    exact Quad4.odd_re_prodFrom f hre _ _
  have gim : ∀ j, ExactTwo k (g j).im := by
    intro j
    simpa [g, L] using exactTwo_prodFrom_pow f hre him hshift (start + j * L) k
  have hblocks_prod :
      Quad4.prodFrom g 0 blocks = Quad4.prodFrom f start (blocks * L) := by
    induction blocks with
    | zero => simp [Quad4.prodFrom]
    | succ b ih =>
        rw [Quad4.prodFrom_succ, ih]
        rw [Nat.succ_mul, Quad4.prodFrom_add]
        congr 2
        simp
  rcases scaledParity_prodFrom g gre gim 0 blocks with ⟨u, hu, huodd⟩
  have hu' : Odd u := huodd.mpr (by exact_mod_cast hblocks_odd)
  refine ⟨u, hu', ?_⟩
  change (Quad4.prodFrom f start len).im = (2 : ℤ) ^ k * u
  rw [← hlen_eq, ← hblocks_prod, hu]

/- ## The A105751 four-factor blocks -/

def blockE (n : ℕ) : ℤ :=
  let x : ℤ := n
  128 * x ^ 4 + 320 * x ^ 3 + 232 * x ^ 2 + 40 * x - 5

def blockF (n : ℕ) : ℤ :=
  let x : ℤ := n
  (x + 1) * (4 * x + 1) * (8 * x + 5)

/-- After extracting the factor `2` from one four-term block. -/
def smallBlock (n : ℕ) : Quad4 := ⟨blockE n, -blockF n⟩

def normalizedFourBlockProduct (m : ℕ) : Quad4 :=
  Quad4.prodFrom smallBlock 0 m

def evenARed (n : ℕ) : ℤ :=
  let x : ℤ := n
  1048576 * x ^ 8 + 4718592 * x ^ 7 + 8486912 * x ^ 6 + 7741440 * x ^ 5 +
    3668224 * x ^ 4 + 741888 * x ^ 3 - 33632 * x ^ 2 - 34920 * x

def evenHRed (n : ℕ) : ℤ :=
  let x : ℤ := n
  262144 * x ^ 7 + 1032192 * x ^ 6 + 1648640 * x ^ 5 + 1370880 * x ^ 4 +
    631456 * x ^ 3 + 157248 * x ^ 2 + 18715 * x

def evenA (n : ℕ) : ℤ := -13975 + 4 * evenARed n
def evenH (n : ℕ) : ℤ := 2925 + 4 * evenHRed n
def evenSuperBlock (n : ℕ) : Quad4 := ⟨evenA n, -evenH n⟩

def oddARed (n : ℕ) : ℤ :=
  let x : ℤ := n
  1048576 * x ^ 8 + 524288 * x ^ 7 - 688128 * x ^ 6 - 286720 * x ^ 5 +
    84224 * x ^ 4 + 28672 * x ^ 3 - 2272 * x ^ 2 - 520 * x

def oddHRed (n : ℕ) : ℤ :=
  let x : ℤ := n
  262144 * x ^ 7 + 114688 * x ^ 6 - 71680 * x ^ 5 - 26880 * x ^ 4 +
    4256 * x ^ 3 + 1232 * x ^ 2 - 45 * x

def oddA (n : ℕ) : ℤ := 25 + 4 * oddARed n
def oddH (n : ℕ) : ℤ := -25 + 4 * oddHRed n
def oddSuperBlock (n : ℕ) : Quad4 := ⟨oddA n, -oddH n⟩

theorem smallBlock_re_odd (n : ℕ) : Odd (smallBlock n).re := by
  refine ⟨64 * (n : ℤ) ^ 4 + 160 * (n : ℤ) ^ 3 + 116 * (n : ℤ) ^ 2 +
    20 * n - 3, ?_⟩
  change blockE n = _
  simp [blockE]
  ring

theorem evenSuperBlock_re_odd (n : ℕ) : Odd (evenSuperBlock n).re := by
  change Odd (evenA n)
  refine (by norm_num : Odd (-13975 : ℤ)).add_even ?_
  refine ⟨2 * evenARed n, ?_⟩
  ring

theorem evenSuperBlock_im_odd (n : ℕ) : Odd (evenSuperBlock n).im := by
  have h : Odd (evenH n) := by
    refine (by norm_num : Odd (2925 : ℤ)).add_even ?_
    exact ⟨2 * evenHRed n, by ring⟩
  change Odd (-evenH n)
  exact h.neg

theorem oddSuperBlock_re_odd (n : ℕ) : Odd (oddSuperBlock n).re := by
  change Odd (oddA n)
  refine (by norm_num : Odd (25 : ℤ)).add_even ?_
  exact ⟨2 * oddARed n, by ring⟩

theorem oddSuperBlock_im_odd (n : ℕ) : Odd (oddSuperBlock n).im := by
  have h : Odd (oddH n) := by
    refine (by norm_num : Odd (-25 : ℤ)).add_even ?_
    exact ⟨2 * oddHRed n, by ring⟩
  change Odd (-oddH n)
  exact h.neg

theorem evenSuperBlock_eq (n : ℕ) :
    Quad4.mul (smallBlock (2 * n)) (smallBlock (2 * n + 1)) = evenSuperBlock n := by
  ext <;>
    simp [Quad4.mul, smallBlock, blockE, blockF, evenSuperBlock, evenA, evenH,
      evenARed, evenHRed] <;>
    ring

theorem oddSuperBlock_eq_pair (n : ℕ) :
    Quad4.mul (smallBlock (2 * n + 1)) (smallBlock (2 * n + 2)) =
      oddSuperBlock (n + 1) := by
  ext <;>
    simp [Quad4.mul, smallBlock, blockE, blockF, oddSuperBlock, oddA, oddH,
      oddARed, oddHRed] <;>
    ring

theorem oddSuperBlock_zero :
    oddSuperBlock 0 = Quad4.mul ⟨-5, 0⟩ (smallBlock 0) := by
  ext <;> norm_num [Quad4.mul, oddSuperBlock, oddA, oddH, oddARed, oddHRed,
    smallBlock, blockE, blockF]

theorem polynomial_shift_dvd (p : Polynomial ℤ) (x d : ℕ) :
    (d : ℤ) ∣ p.eval ((x + d : ℕ) : ℤ) - p.eval (x : ℤ) := by
  simpa using Polynomial.sub_dvd_eval_sub ((x + d : ℕ) : ℤ) (x : ℤ) p

theorem evenARed_shift_dvd (x d : ℕ) :
    (d : ℤ) ∣ evenARed (x + d) - evenARed x := by
  let p : Polynomial ℤ :=
    1048576 * Polynomial.X ^ 8 + 4718592 * Polynomial.X ^ 7 +
    8486912 * Polynomial.X ^ 6 + 7741440 * Polynomial.X ^ 5 +
    3668224 * Polynomial.X ^ 4 + 741888 * Polynomial.X ^ 3 -
    33632 * Polynomial.X ^ 2 - 34920 * Polynomial.X
  simpa [p, evenARed] using polynomial_shift_dvd p x d

theorem evenHRed_shift_dvd (x d : ℕ) :
    (d : ℤ) ∣ evenHRed (x + d) - evenHRed x := by
  let p : Polynomial ℤ :=
    262144 * Polynomial.X ^ 7 + 1032192 * Polynomial.X ^ 6 +
    1648640 * Polynomial.X ^ 5 + 1370880 * Polynomial.X ^ 4 +
    631456 * Polynomial.X ^ 3 + 157248 * Polynomial.X ^ 2 +
    18715 * Polynomial.X
  simpa [p, evenHRed] using polynomial_shift_dvd p x d

theorem oddARed_shift_dvd (x d : ℕ) :
    (d : ℤ) ∣ oddARed (x + d) - oddARed x := by
  let p : Polynomial ℤ :=
    1048576 * Polynomial.X ^ 8 + 524288 * Polynomial.X ^ 7 -
    688128 * Polynomial.X ^ 6 - 286720 * Polynomial.X ^ 5 +
    84224 * Polynomial.X ^ 4 + 28672 * Polynomial.X ^ 3 -
    2272 * Polynomial.X ^ 2 - 520 * Polynomial.X
  simpa [p, oddARed] using polynomial_shift_dvd p x d

theorem oddHRed_shift_dvd (x d : ℕ) :
    (d : ℤ) ∣ oddHRed (x + d) - oddHRed x := by
  let p : Polynomial ℤ :=
    262144 * Polynomial.X ^ 7 + 114688 * Polynomial.X ^ 6 -
    71680 * Polynomial.X ^ 5 - 26880 * Polynomial.X ^ 4 +
    4256 * Polynomial.X ^ 3 + 1232 * Polynomial.X ^ 2 -
    45 * Polynomial.X
  simpa [p, oddHRed] using polynomial_shift_dvd p x d

theorem const_add_four_shift_dvd (r : ℕ → ℤ)
    (hr : ∀ (x d : ℕ), (d : ℤ) ∣ r (x + d) - r x) (c : ℤ) (x d : ℕ) :
    (4 : ℤ) * (d : ℤ) ∣ (c + 4 * r x) - (c + 4 * r (x + d)) := by
  rcases hr x d with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  calc
    (c + 4 * r x) - (c + 4 * r (x + d)) = -4 * (r (x + d) - r x) := by ring
    _ = (4 : ℤ) * (d : ℤ) * (-q) := by rw [hq]; ring

theorem cross_shift_of_component_shift
    (f : ℕ → Quad4)
    (hre : ∀ (x d : ℕ), (4 : ℤ) * (d : ℤ) ∣ (f x).re - (f (x + d)).re)
    (him : ∀ (x d : ℕ), (4 : ℤ) * (d : ℤ) ∣ (f x).im - (f (x + d)).im)
    (x d : ℕ) :
    (4 : ℤ) * (d : ℤ) ∣ Quad4.cross (f x) (f (x + d)) := by
  have hr := hre x d
  have hi := him x d
  have hcomb : (4 : ℤ) * (d : ℤ) ∣
      ((f x).im - (f (x + d)).im) * (f (x + d)).re -
        ((f x).re - (f (x + d)).re) * (f (x + d)).im :=
    dvd_sub (dvd_mul_of_dvd_left hi _) (dvd_mul_of_dvd_left hr _)
  have heq :
      Quad4.cross (f x) (f (x + d)) =
        ((f x).im - (f (x + d)).im) * (f (x + d)).re -
          ((f x).re - (f (x + d)).re) * (f (x + d)).im := by
    simp only [Quad4.cross]
    ring
  rw [heq]
  exact hcomb

theorem evenSuperBlock_cross_shift (x d : ℕ) :
    (4 : ℤ) * (d : ℤ) ∣ Quad4.cross (evenSuperBlock x) (evenSuperBlock (x + d)) := by
  apply cross_shift_of_component_shift evenSuperBlock
  · intro a b
    simpa [evenSuperBlock, evenA] using
      const_add_four_shift_dvd evenARed evenARed_shift_dvd (-13975) a b
  · intro a b
    have h := const_add_four_shift_dvd evenHRed evenHRed_shift_dvd 2925 a b
    rcases h with ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    change -evenH a - -evenH (a + b) = (4 : ℤ) * (b : ℤ) * (-q)
    change evenH a - evenH (a + b) = (4 : ℤ) * (b : ℤ) * q at hq
    linear_combination -hq

theorem oddSuperBlock_cross_shift (x d : ℕ) :
    (4 : ℤ) * (d : ℤ) ∣ Quad4.cross (oddSuperBlock x) (oddSuperBlock (x + d)) := by
  apply cross_shift_of_component_shift oddSuperBlock
  · intro a b
    simpa [oddSuperBlock, oddA] using
      const_add_four_shift_dvd oddARed oddARed_shift_dvd 25 a b
  · intro a b
    have h := const_add_four_shift_dvd oddHRed oddHRed_shift_dvd (-25) a b
    rcases h with ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    change -oddH a - -oddH (a + b) = (4 : ℤ) * (b : ℤ) * (-q)
    change oddH a - oddH (a + b) = (4 : ℤ) * (b : ℤ) * q at hq
    linear_combination -hq

/- Regrouping the normalized four-term blocks into the two superblock families. -/

theorem normalizedFourBlockProduct_even (q : ℕ) :
    normalizedFourBlockProduct (2 * q) = Quad4.prodFrom evenSuperBlock 0 q := by
  induction q with
  | zero => simp [normalizedFourBlockProduct]
  | succ q ih =>
      rw [normalizedFourBlockProduct] at ih
      rw [show 2 * (q + 1) = 2 * q + 2 by omega]
      rw [normalizedFourBlockProduct, Quad4.prodFrom_add, ih]
      rw [Quad4.prodFrom_succ]
      congr 1
      rw [Quad4.prodFrom_succ, Quad4.prodFrom_zero,
        Quad4.one_mul]
      rw [show 0 + 2 * q + 0 = 2 * q by omega,
        show 0 + 2 * q + 1 = 2 * q + 1 by omega,
        show 0 + q = q by omega]
      exact evenSuperBlock_eq q

theorem oddSuperBlock_tail (q : ℕ) :
    Quad4.prodFrom oddSuperBlock 1 q = Quad4.prodFrom smallBlock 1 (2 * q) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Quad4.prodFrom_succ, ih]
      rw [show 2 * (q + 1) = 2 * q + 2 by omega]
      rw [Quad4.prodFrom_add]
      congr 1
      rw [Quad4.prodFrom_succ]
      rw [Quad4.prodFrom_succ, Quad4.prodFrom_zero, Quad4.one_mul]
      rw [show 1 + q = q + 1 by omega,
        show 1 + 2 * q + 0 = 2 * q + 1 by omega,
        show 1 + 2 * q + 1 = 2 * q + 2 by omega]
      exact (oddSuperBlock_eq_pair q).symm

theorem oddSuperBlock_product (q : ℕ) :
    Quad4.prodFrom oddSuperBlock 0 (q + 1) =
      Quad4.mul ⟨-5, 0⟩ (normalizedFourBlockProduct (2 * q + 1)) := by
  rw [show q + 1 = 1 + q by omega]
  rw [Quad4.prodFrom_add oddSuperBlock 0 1 q]
  rw [show 2 * q + 1 = 1 + 2 * q by omega]
  rw [normalizedFourBlockProduct]
  rw [Quad4.prodFrom_add smallBlock 0 1 (2 * q)]
  rw [oddSuperBlock_tail]
  simp only [Quad4.prodFrom_succ, Quad4.prodFrom_zero, Quad4.one_mul,
    zero_add]
  rw [oddSuperBlock_zero, Quad4.mul_assoc]

theorem exactTwo_normalized_even (q : ℕ) (hq : q ≠ 0) :
    ExactTwo (padicValNat 2 q) (normalizedFourBlockProduct (2 * q)).im := by
  rw [normalizedFourBlockProduct_even]
  exact exactTwo_prodFrom evenSuperBlock evenSuperBlock_re_odd
    evenSuperBlock_im_odd evenSuperBlock_cross_shift 0 q hq

theorem exactTwo_normalized_odd (q : ℕ) :
    ExactTwo (padicValNat 2 (q + 1)) (normalizedFourBlockProduct (2 * q + 1)).im := by
  have hprod := exactTwo_prodFrom oddSuperBlock oddSuperBlock_re_odd
    oddSuperBlock_im_odd oddSuperBlock_cross_shift 0 (q + 1) (by omega)
  rw [oddSuperBlock_product] at hprod
  have him : (Quad4.mul ⟨-5, 0⟩ (normalizedFourBlockProduct (2 * q + 1))).im =
      (normalizedFourBlockProduct (2 * q + 1)).im * (-5) := by
    simp [Quad4.mul]
    ring
  rw [him] at hprod
  exact ExactTwo.of_mul_odd hprod (by norm_num)

/- ## Connection with the Gaussian-integer product defining A105751 -/

def Quad4.toGaussian (z : Quad4) : GaussianInt := ⟨z.re, 4 * z.im⟩

theorem Quad4.toGaussian_mul (z w : Quad4) :
    Quad4.toGaussian (Quad4.mul z w) = Quad4.toGaussian z * Quad4.toGaussian w := by
  ext <;> simp [Quad4.toGaussian, Quad4.mul] <;> ring

def gaussianFactor (n : ℕ) : GaussianInt := ⟨1, n⟩

def gaussianProduct (n : ℕ) : GaussianInt :=
  (Finset.range (n + 1)).prod gaussianFactor

theorem gaussianProduct_toComplex (n : ℕ) :
    ((gaussianProduct n : GaussianInt) : ℂ) =
      (Finset.range (n + 1)).prod (fun k : ℕ ↦ 1 + (k : ℂ) * I) := by
  simp [gaussianProduct, gaussianFactor, map_prod, GaussianInt.toComplex_def]

noncomputable def sequenceA (n : ℕ) : ℤ :=
  let productTerm (k : ℕ) : ℂ := 1 + (k : ℂ) * I
  Int.floor (((Finset.range (n + 1)).prod productTerm).im)

theorem sequenceA_eq_gaussianProduct_im (n : ℕ) :
    sequenceA n = (gaussianProduct n).im := by
  rw [sequenceA]
  rw [← gaussianProduct_toComplex]
  simpa using (Int.floor_intCast (R := ℝ) (gaussianProduct n).im)

theorem gaussianProduct_succ (n : ℕ) :
    gaussianProduct (n + 1) = gaussianProduct n * gaussianFactor (n + 1) := by
  simp [gaussianProduct, Finset.prod_range_succ]

theorem gaussianFourBlock (m : ℕ) :
    gaussianFactor (4 * m + 1) * gaussianFactor (4 * m + 2) *
        gaussianFactor (4 * m + 3) * gaussianFactor (4 * m + 4) =
      (2 : GaussianInt) * Quad4.toGaussian (smallBlock m) := by
  ext <;>
    simp [gaussianFactor, Quad4.toGaussian, smallBlock, blockE, blockF] <;>
    ring

theorem normalizedFourBlockProduct_succ (m : ℕ) :
    normalizedFourBlockProduct (m + 1) =
      Quad4.mul (normalizedFourBlockProduct m) (smallBlock m) := by
  simp [normalizedFourBlockProduct, Quad4.prodFrom_succ]

theorem gaussianProduct_four (m : ℕ) :
    gaussianProduct (4 * m) =
      (2 : GaussianInt) ^ m * Quad4.toGaussian (normalizedFourBlockProduct m) := by
  induction m with
  | zero =>
      norm_num [gaussianProduct, gaussianFactor, normalizedFourBlockProduct,
        Quad4.prodFrom, Quad4.toGaussian]
  | succ m ih =>
      have hstep : gaussianProduct (4 * (m + 1)) =
          gaussianProduct (4 * m) * gaussianFactor (4 * m + 1) *
            gaussianFactor (4 * m + 2) * gaussianFactor (4 * m + 3) *
              gaussianFactor (4 * m + 4) := by
        rw [show 4 * (m + 1) = (((4 * m + 1) + 1) + 1) + 1 by omega]
        rw [gaussianProduct_succ, gaussianProduct_succ, gaussianProduct_succ,
          gaussianProduct_succ]
      rw [hstep, ih]
      rw [normalizedFourBlockProduct_succ, Quad4.toGaussian_mul]
      rw [show
        (2 : GaussianInt) ^ m * Quad4.toGaussian (normalizedFourBlockProduct m) *
              gaussianFactor (4 * m + 1) * gaussianFactor (4 * m + 2) *
                gaussianFactor (4 * m + 3) * gaussianFactor (4 * m + 4) =
            ((2 : GaussianInt) ^ m * Quad4.toGaussian (normalizedFourBlockProduct m)) *
              (gaussianFactor (4 * m + 1) * gaussianFactor (4 * m + 2) *
                gaussianFactor (4 * m + 3) * gaussianFactor (4 * m + 4)) by ring]
      rw [gaussianFourBlock]
      simp only [pow_succ]
      ring

@[simp] theorem gaussian_two_pow (m : ℕ) :
    (2 : GaussianInt) ^ m = ⟨(2 : ℤ) ^ m, 0⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ, ih]
      ext <;> simp [pow_succ]

theorem sequenceA_four (m : ℕ) :
    sequenceA (4 * m) =
      (2 : ℤ) ^ (m + 2) * (normalizedFourBlockProduct m).im := by
  rw [sequenceA_eq_gaussianProduct_im, gaussianProduct_four]
  simp [Quad4.toGaussian, pow_add]
  ring

theorem sequenceA_four_add_one (m : ℕ) :
    sequenceA (4 * m + 1) = (2 : ℤ) ^ m *
      ((4 * (m : ℤ) + 1) * (normalizedFourBlockProduct m).re +
        4 * (normalizedFourBlockProduct m).im) := by
  rw [sequenceA_eq_gaussianProduct_im]
  rw [show 4 * m + 1 = 4 * m + 1 by rfl, gaussianProduct_succ]
  rw [gaussianProduct_four]
  simp [gaussianFactor, Quad4.toGaussian]
  ring

theorem sequenceA_four_add_two (m : ℕ) :
    sequenceA (4 * m + 2) = (2 : ℤ) ^ m *
      ((8 * (m : ℤ) + 3) * (normalizedFourBlockProduct m).re -
        4 * (16 * (m : ℤ) ^ 2 + 12 * (m : ℤ) + 1) *
          (normalizedFourBlockProduct m).im) := by
  rw [sequenceA_eq_gaussianProduct_im]
  rw [show 4 * m + 2 = (4 * m + 1) + 1 by omega]
  rw [gaussianProduct_succ, gaussianProduct_succ, gaussianProduct_four]
  simp [gaussianFactor, Quad4.toGaussian]
  ring

theorem sequenceA_four_add_three (m : ℕ) :
    sequenceA (4 * m + 3) = -(2 : ℤ) ^ (m + 3) *
      ((24 * (m : ℤ) ^ 2 + 24 * (m : ℤ) + 5) *
          (normalizedFourBlockProduct m).im +
        4 * (m : ℤ) * ((m : ℤ) + 1) * (2 * (m : ℤ) + 1) *
          (normalizedFourBlockProduct m).re) := by
  rw [sequenceA_eq_gaussianProduct_im]
  rw [show 4 * m + 3 = ((4 * m + 1) + 1) + 1 by omega]
  rw [gaussianProduct_succ, gaussianProduct_succ, gaussianProduct_succ,
    gaussianProduct_four]
  simp [gaussianFactor, Quad4.toGaussian, pow_add]
  ring

/- ## Exact valuations in the four residue classes -/

theorem ExactTwo.pow_mul_left {k : ℕ} {z : ℤ} (hz : ExactTwo k z) (r : ℕ) :
    ExactTwo (r + k) ((2 : ℤ) ^ r * z) := by
  rcases hz with ⟨u, hu, rfl⟩
  refine ⟨u, hu, ?_⟩
  rw [pow_add]
  ring

theorem ExactTwo.add_higher {k : ℕ} {z t c : ℤ}
    (hz : ExactTwo k z) (hc : Odd c) (ht : (2 : ℤ) ^ (k + 1) ∣ t) :
    ExactTwo k (c * z + t) := by
  rcases hz with ⟨u, hu, rfl⟩
  rcases ht with ⟨v, rfl⟩
  refine ⟨c * u + 2 * v, (hc.mul hu).add_even ⟨v, by ring⟩, ?_⟩
  rw [pow_succ]
  ring

theorem exactTwo_normalized_half (m : ℕ) (hm : m ≠ 0) :
    ExactTwo (padicValNat 2 ((m + 1) / 2))
      (normalizedFourBlockProduct m).im := by
  obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' m
  · subst m
    have hq0 : q ≠ 0 := by omega
    have h := exactTwo_normalized_even q hq0
    have hhalf : (2 * q + 1) / 2 = q := by omega
    rwa [hhalf]
  · subst m
    have h := exactTwo_normalized_odd q
    have hhalf : (2 * q + 1 + 1) / 2 = q + 1 := by omega
    rwa [hhalf]

theorem twice_half_dvd_consecutive (m : ℕ) :
    (2 : ℤ) * (((m + 1) / 2 : ℕ) : ℤ) ∣ (m : ℤ) * ((m : ℤ) + 1) := by
  obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' m
  · subst m
    have hhalf : (2 * q + 1) / 2 = q := by omega
    rw [hhalf]
    refine ⟨(2 * q + 1 : ℕ), ?_⟩
    norm_num
  · subst m
    have hhalf : (2 * q + 1 + 1) / 2 = q + 1 := by omega
    rw [hhalf]
    refine ⟨(2 * q + 1 : ℕ), ?_⟩
    norm_num
    ring

theorem higher_term_dvd (m : ℕ) :
    (2 : ℤ) ^ (padicValNat 2 ((m + 1) / 2) + 1) ∣
      4 * (m : ℤ) * ((m : ℤ) + 1) * (2 * (m : ℤ) + 1) *
        (normalizedFourBlockProduct m).re := by
  let h := (m + 1) / 2
  let k := padicValNat 2 h
  have hpowNat : 2 ^ k ∣ h := pow_padicValNat_dvd (p := 2) (n := h)
  have hpow : (2 : ℤ) ^ k ∣ (h : ℤ) := by exact_mod_cast hpowNat
  have hpair : (2 : ℤ) * (h : ℤ) ∣ (m : ℤ) * ((m : ℤ) + 1) := by
    simpa [h] using twice_half_dvd_consecutive m
  rcases hpow with ⟨d, hd⟩
  rcases hpair with ⟨e, he⟩
  refine ⟨4 * d * e * (2 * (m : ℤ) + 1) *
    (normalizedFourBlockProduct m).re, ?_⟩
  change 4 * (m : ℤ) * ((m : ℤ) + 1) * (2 * (m : ℤ) + 1) *
      (normalizedFourBlockProduct m).re = (2 : ℤ) ^ (k + 1) * _
  calc
    4 * (m : ℤ) * ((m : ℤ) + 1) * (2 * (m : ℤ) + 1) *
        (normalizedFourBlockProduct m).re =
      4 * ((m : ℤ) * ((m : ℤ) + 1)) * (2 * (m : ℤ) + 1) *
        (normalizedFourBlockProduct m).re := by ring
    _ = (2 : ℤ) ^ (k + 1) *
        (4 * d * e * (2 * (m : ℤ) + 1) *
          (normalizedFourBlockProduct m).re) := by
      rw [he, hd, pow_succ]
      ring

theorem exactTwo_sequenceA_four (m : ℕ) (hm : m ≠ 0) :
    ExactTwo (m + 2 + padicValNat 2 ((m + 1) / 2)) (sequenceA (4 * m)) := by
  rw [sequenceA_four]
  exact (exactTwo_normalized_half m hm).pow_mul_left (m + 2)

theorem exactTwo_sequenceA_four_add_one (m : ℕ) :
    ExactTwo m (sequenceA (4 * m + 1)) := by
  rw [sequenceA_four_add_one]
  apply ExactTwo.pow_mul_left (k := 0) (r := m)
  rw [exactTwo_zero_iff_odd]
  apply Odd.add_even
  · have hre : Odd (normalizedFourBlockProduct m).re := by
      exact Quad4.odd_re_prodFrom smallBlock smallBlock_re_odd 0 m
    exact (show Odd (4 * (m : ℤ) + 1) from ⟨2 * (m : ℤ), by ring⟩).mul hre
  · exact ⟨2 * (normalizedFourBlockProduct m).im, by ring⟩

theorem exactTwo_sequenceA_four_add_two (m : ℕ) :
    ExactTwo m (sequenceA (4 * m + 2)) := by
  rw [sequenceA_four_add_two]
  apply ExactTwo.pow_mul_left (k := 0) (r := m)
  rw [exactTwo_zero_iff_odd]
  apply Odd.sub_even
  · exact (show Odd (8 * (m : ℤ) + 3) from ⟨4 * (m : ℤ) + 1, by ring⟩).mul
      (by exact Quad4.odd_re_prodFrom smallBlock smallBlock_re_odd 0 m)
  · exact ⟨2 * (16 * (m : ℤ) ^ 2 + 12 * (m : ℤ) + 1) *
      (normalizedFourBlockProduct m).im, by ring⟩

theorem exactTwo_sequenceA_four_add_three (m : ℕ) (hm : m ≠ 0) :
    ExactTwo (m + 3 + padicValNat 2 ((m + 1) / 2))
      (sequenceA (4 * m + 3)) := by
  rw [sequenceA_four_add_three]
  have hbracket : ExactTwo (padicValNat 2 ((m + 1) / 2))
      ((24 * (m : ℤ) ^ 2 + 24 * (m : ℤ) + 5) *
          (normalizedFourBlockProduct m).im +
        4 * (m : ℤ) * ((m : ℤ) + 1) * (2 * (m : ℤ) + 1) *
          (normalizedFourBlockProduct m).re) := by
    apply ExactTwo.add_higher (exactTwo_normalized_half m hm)
    · exact ⟨12 * (m : ℤ) ^ 2 + 12 * (m : ℤ) + 2, by ring⟩
    · exact higher_term_dvd m
  have hpos := hbracket.pow_mul_left (m + 3)
  simpa only [neg_mul] using hpos.neg

theorem padicValInt_two_pow (k : ℕ) :
    padicValInt 2 ((2 : ℤ) ^ k) = k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      rw [padicValInt.mul (pow_ne_zero _ (by norm_num)) (by norm_num)]
      have hself : padicValInt 2 (2 : ℤ) = 1 := padicValInt_self
      rw [ih, hself]

theorem ExactTwo.padicValInt_eq {k : ℕ} {z : ℤ} (hz : ExactTwo k z) :
    padicValInt 2 z = k := by
  rcases hz with ⟨u, hu, rfl⟩
  rcases hu with ⟨w, hw⟩
  have hu0 : u ≠ 0 := by
    intro h
    omega
  have hnot : ¬(2 : ℤ) ∣ u := by
    intro hd
    rcases hd with ⟨v, hv⟩
    omega
  rw [padicValInt.mul (pow_ne_zero _ (by norm_num)) hu0]
  rw [padicValInt_two_pow, padicValInt.eq_zero_of_not_dvd hnot]
  omega

theorem padicValInt_sequenceA_four (m : ℕ) (hm : m ≠ 0) :
    padicValInt 2 (sequenceA (4 * m)) =
      m + 2 + padicValNat 2 ((m + 1) / 2) :=
  (exactTwo_sequenceA_four m hm).padicValInt_eq

theorem padicValInt_sequenceA_four_add_one (m : ℕ) :
    padicValInt 2 (sequenceA (4 * m + 1)) = m :=
  (exactTwo_sequenceA_four_add_one m).padicValInt_eq

theorem padicValInt_sequenceA_four_add_two (m : ℕ) :
    padicValInt 2 (sequenceA (4 * m + 2)) = m :=
  (exactTwo_sequenceA_four_add_two m).padicValInt_eq

theorem padicValInt_sequenceA_four_add_three (m : ℕ) (hm : m ≠ 0) :
    padicValInt 2 (sequenceA (4 * m + 3)) =
      m + 3 + padicValNat 2 ((m + 1) / 2) :=
  (exactTwo_sequenceA_four_add_three m hm).padicValInt_eq

/- ## The asymptotic limit -/

theorem tendsto_nat_log_div_real :
    Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  have hreal : Tendsto (fun x : ℝ ↦ Real.logb 2 x / x) atTop (nhds 0) :=
    (Real.isLittleO_logb_id_atTop (b := 2)).tendsto_div_nhds_zero
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ div_nonneg (by positivity) (by positivity)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    apply div_le_div_of_nonneg_right (Real.natLog_le_logb n 2) (by positivity)
  · simpa [Function.comp_def] using hnat

theorem asymptotic_error_bound (n : ℕ) (hn : 4 ≤ n) :
    |(4 : ℝ) * (padicValInt 2 (sequenceA n) : ℝ) / (n : ℝ) - 1| ≤
      ((12 : ℝ) + 4 * (Nat.log 2 n : ℝ)) / (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by positivity
  rw [show (4 : ℝ) * (padicValInt 2 (sequenceA n) : ℝ) / (n : ℝ) - 1 =
      ((4 : ℝ) * (padicValInt 2 (sequenceA n) : ℝ) - (n : ℝ)) / (n : ℝ) by
    field_simp]
  rw [abs_div, abs_of_pos hnpos]
  apply div_le_div_of_nonneg_right _ hnpos.le
  let m := n / 4
  let r := n % 4
  have hr : r < 4 := by
    dsimp [r]
    exact Nat.mod_lt _ (by omega)
  have hrep : n = 4 * m + r := by
    dsimp [m, r]
    have h := Nat.mod_add_div n 4
    omega
  rw [hrep]
  interval_cases r
  · have hm0 : m ≠ 0 := by omega
    rw [show 4 * m + 0 = 4 * m by omega, padicValInt_sequenceA_four m hm0]
    have hk := padicValNat_le_nat_log (p := 2) ((m + 1) / 2)
    have hmono : Nat.log 2 ((m + 1) / 2) ≤ Nat.log 2 (4 * m) :=
      Nat.log_mono_right (by omega)
    have hbound : padicValNat 2 ((m + 1) / 2) ≤ Nat.log 2 (4 * m) :=
      hk.trans hmono
    have hnum :
        (4 : ℝ) * (m + 2 + padicValNat 2 ((m + 1) / 2) : ℕ) - (4 * m : ℕ) =
          8 + 4 * (padicValNat 2 ((m + 1) / 2) : ℝ) := by
      push_cast
      ring
    rw [hnum, abs_of_nonneg (by positivity)]
    exact_mod_cast (by omega :
      8 + 4 * padicValNat 2 ((m + 1) / 2) ≤ 12 + 4 * Nat.log 2 (4 * m))
  · rw [padicValInt_sequenceA_four_add_one]
    have hnum : (4 : ℝ) * (m : ℝ) - (4 * m + 1 : ℕ) = -1 := by
      push_cast
      ring
    rw [hnum]
    norm_num
    have hlog : 0 ≤ (Nat.log 2 (4 * m + 1) : ℝ) := by positivity
    linarith
  · rw [padicValInt_sequenceA_four_add_two]
    have hnum : (4 : ℝ) * (m : ℝ) - (4 * m + 2 : ℕ) = -2 := by
      push_cast
      ring
    rw [hnum]
    norm_num
    have hlog : 0 ≤ (Nat.log 2 (4 * m + 2) : ℝ) := by positivity
    linarith
  · have hm0 : m ≠ 0 := by omega
    rw [padicValInt_sequenceA_four_add_three m hm0]
    have hk := padicValNat_le_nat_log (p := 2) ((m + 1) / 2)
    have hmono : Nat.log 2 ((m + 1) / 2) ≤ Nat.log 2 (4 * m + 3) :=
      Nat.log_mono_right (by omega)
    have hbound : padicValNat 2 ((m + 1) / 2) ≤ Nat.log 2 (4 * m + 3) :=
      hk.trans hmono
    have hnum :
        (4 : ℝ) * (m + 3 + padicValNat 2 ((m + 1) / 2) : ℕ) -
            (4 * m + 3 : ℕ) =
          9 + 4 * (padicValNat 2 ((m + 1) / 2) : ℝ) := by
      push_cast
      ring
    rw [hnum, abs_of_nonneg (by positivity)]
    exact_mod_cast (by omega :
      9 + 4 * padicValNat 2 ((m + 1) / 2) ≤
        12 + 4 * Nat.log 2 (4 * m + 3))

theorem tendsto_error_bound_real :
    Tendsto (fun n : ℕ ↦ ((12 : ℝ) + 4 * (Nat.log 2 n : ℝ)) / (n : ℝ))
      atTop (nhds 0) := by
  have hc : Tendsto (fun n : ℕ ↦ (12 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 12
  have hl := tendsto_nat_log_div_real.const_mul (4 : ℝ)
  convert hc.add hl using 1
  · ext n
    ring
  · norm_num

theorem sequenceA_limit_real :
    Tendsto
      (fun n : ℕ ↦ (4 : ℝ) * (padicValInt 2 (sequenceA n) : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ ↦ dist_nonneg
  · filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
    simpa [Real.dist_eq] using asymptotic_error_bound n hn
  · exact tendsto_error_bound_real

theorem sequenceA_conjecture :
    Tendsto
      (fun n : ℕ ↦ (4 : ℚ) * (padicValInt 2 (sequenceA n) : ℚ) / (n : ℚ))
      atTop (nhds 1) := by
  rw [Rat.isEmbedding_coe_real.tendsto_nhds_iff]
  simpa [Function.comp_def] using sequenceA_limit_real

#print axioms sequenceA_conjecture

end A105751Proof
