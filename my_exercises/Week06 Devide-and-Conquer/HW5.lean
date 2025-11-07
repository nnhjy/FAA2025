import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false


-- # Problem 1: Finding Min Recursively
def minimum (a b:ℕ ): ℕ := if a < b then a else b

-- Consider the following FindMin function
def FindMin (l : List ℕ) : ℕ :=
  match h: l with
  | [] => 0   -- Base case for empty list (0 is minimum in ℕ)
  | x::xs =>
    if he: xs = [] then x
    else
      have: 1 < l.length := by
        simp [h]
        by_contra!
        observe: xs.length = 0
        simp_all only [le_refl, List.length_eq_zero_iff]
      let n := l.length
      let left  := l.take (n / 2)
      let right := l.drop (n / 2)
      -- Recursive step: find max of each half and compare
      minimum (FindMin left) (FindMin right)
termination_by l.length decreasing_by all_goals grind

def Nat.MinOfList (a :ℕ ) (t: List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- You can use the following APIs.
-- # In this problem, prove that the FindMin algorithm correctly returns the minimum element for any non-empty input list of size n.
-- You may find the following theorems useful
theorem x_minlist_of_x_lt_minlist {x y: ℕ} {l: List ℕ }
(h1: x ≤ y) (h2 : y.MinOfList l)
: x.MinOfList l := by grind [Nat.MinOfList]
theorem min_list_of_left_right {x : ℕ} {l : List ℕ}
(left right: List ℕ) (h_lr: left ++ right = l)
(h_min_left: x.MinOfList left)(h_min_right: x.MinOfList right)
: x.MinOfList (l) := by grind [Nat.MinOfList]


theorem Problem1 (l : List ℕ) (h_nonempty : l.length > 0) :
  let z := FindMin l
  z.MinOfList l := by
  fun_induction FindMin l
  · grind
  · simp [Nat.MinOfList]
  · let min_left := FindMin left
    let min_right := FindMin right

    replace ih2 : min_left.MinOfList left := by grind
    -- have ih_left : min_left.MinOfList left := by grind
    replace ih1 : min_right.MinOfList right := by grind
    have h_lr : left ++ right = x :: xs := by aesop
      -- rw [← List.take_append_drop (n / 2) (x :: xs)]

    intro hz
    have hz_le_min_left : hz ≤ min_left := by
      simp only [hz]
      simp only [minimum]
      split_ifs with h_cmp
      all_goals
      simp only [min_left, left]
      grind
      -- · exact le_refl _
      -- · exact le_of_not_gt h_cmp
    have hz_le_min_right : hz ≤ min_right := by
      simp only [hz]
      simp only [minimum]
      split_ifs with h_cmp
      all_goals
      simp only [min_right, right]
      grind
      -- · exact le_of_lt h_cmp
      -- . exact le_refl _

    have hz_min_left : hz.MinOfList left := by exact x_minlist_of_x_lt_minlist hz_le_min_left ih2
    have hz_min_right : hz.MinOfList right := by exact x_minlist_of_x_lt_minlist hz_le_min_right ih1
    apply min_list_of_left_right left right h_lr hz_min_left hz_min_right

-- # Problem 2: Finding Min Sequentially
-- Define minimum property
def Option.MinOfList (result : Option ℕ) (l : List ℕ) : Prop :=
  match result with
  | none => l = []
  | some m => m ∈ l ∧ ∀ x ∈ l, m ≤ x

def List.minHelper (xs : List ℕ)(val_so_far : ℕ) : ℕ :=
  match xs with
  | [] => val_so_far
  | x :: xs => xs.minHelper (min x val_so_far)

def List.FindMin : List ℕ → Option ℕ
  | [] => none
  | x :: xs => some (xs.minHelper x)

-- # In problem 2, prove that FindMin function correctly compute the mininmum
#print List
-- Auxiliary: the scan never increases the accumulator.
lemma minHelper_le_acc (xs : List ℕ) (a : ℕ) : xs.minHelper a ≤ a := by
  induction xs generalizing a with
  | nil => simp [List.minHelper]
  | cons y ys ih =>
      -- Goal: ys.minHelper (min y a) ≤ a
      have h : ys.minHelper (min y a) ≤ min y a := ih (min y a)
      exact le_trans h (min_le_right _ _)

-- Auxiliary: the minHelper function always generates an infinum of the list
lemma minHelper_inf (z : ℕ) (xs : List ℕ) :
    ∀ x ∈ xs, xs.minHelper z ≤ x := by
  induction xs generalizing z with
  | nil => intro x hx; grind
      -- No elements in []; vacuous
      -- exact (False.elim (by simp at hx))
  | cons y ys ih =>
      intro x hx
      -- xs = y :: ys, result is ys.minHelper (min y z)
      have hx' : x = y ∨ x ∈ ys := by
        simpa [List.mem_cons] using hx
      cases hx' with
      | inl hxy =>
          -- Show ≤ y via ≤ min y z and then min_le_left
          subst hxy
          have hacc : ys.minHelper (min x z) ≤ min x z :=
            minHelper_le_acc ys (min x z)
          simpa [List.minHelper] using le_trans hacc (min_le_left _ _)
      | inr hInYs =>
          -- For tail elements, use IH with updated accumulator
          have h := ih (min y z) x hInYs
          simpa [List.minHelper] using h

-- /--
-- If scanning `xs` with accumulator `x` returns `x`, and `a ≤ x`,
-- then scanning `xs` with accumulator `a` returns `a`.
-- -/
-- lemma minHelper_min_ext (xs : List ℕ) (a x : ℕ)
--   (hx : xs.minHelper x = x)
--   (hax : a ≤ x) : xs.minHelper a = a := by
--   induction xs generalizing a x with
--   | nil =>
--       simp [List.minHelper]
--   | cons y ys ih =>
--       -- We will extract `x ≤ y` from `hx` using `minHelper_le_acc`.
--       -- First, rewrite `hx` to the unfolded form on `y :: ys`.
--       have hx0 : ys.minHelper (min y x) = x := by
--         -- (y :: ys).minHelper x = ys.minHelper (min y x)
--         simpa [List.minHelper] using hx

--       -- From the accumulator monotonicity: ys.minHelper (min y x) ≤ min y x
--       -- rewrite the LHS with `hx0` to conclude `x ≤ min y x`.
--       have x_le_min : x ≤ min y x := by
--         have h := minHelper_le_acc ys (min y x)
--         -- h : ys.minHelper (min y x) ≤ min y x
--         simpa [hx0] using h

--       -- Hence x ≤ y (since x ≤ min y x and min y x ≤ y).
--       have x_le_y : x ≤ y := le_trans x_le_min (min_le_left _ _)

--       -- Therefore a ≤ y by transitivity a ≤ x ≤ y.
--       have a_le_y : a ≤ y := le_trans hax x_le_y

--       -- Prepare the IH premise on the tail:
--       -- 1) Show scanning with (min y x) returns (min y x).
--       have hx' : ys.minHelper (min y x) = min y x := by
--         -- From hx0 and min y x = x (because x ≤ y) rewrite RHS.
--         have minyx_eq : min y x = x := min_eq_right x_le_y
--         simpa [minyx_eq] using hx0

--       -- 2) Monotonicity of min in the second argument: min y a ≤ min y x.
--       have hax' : min y a ≤ min y x := by
--         exact min_le_min_left _ hax

--       -- Apply IH on ys with accumulators (min y a) and (min y x).
--       have ih' := ih (min y a) (min y x) hx' hax'

--       -- Since a ≤ y, min y a = a, so rewrite to finish.
--       have hminay : min y a = a := min_eq_right a_le_y
--       simpa [List.minHelper, hminay] using ih'


/-- Generalized membership: for any accumulator `z`, the result of `xs.minHelper z` lies in `z :: xs`. -/
lemma minHelper_membership (xs : List ℕ) (z : ℕ) : xs.minHelper z ∈ z :: xs := by
  induction xs generalizing z with
  | nil => simp [List.minHelper]
  | cons y ys ih =>
      -- We need: ys.minHelper (min y z) ∈ z :: y :: ys.
      -- From IH we know: ys.minHelper (min y z) ∈ (min y z) :: ys
      have h := ih (min y z)
      -- Split that membership
      have : ys.minHelper (min y z) = min y z ∨ ys.minHelper (min y z) ∈ ys := by
        simpa [List.mem_cons] using h
      cases this with
      | inl hEq =>
          -- The result equals `min y z`; place it in `z :: y :: ys` by cases on `z ≤ y`
          -- (equivalently `y ≤ z`) to decide `min y z`.
          cases le_total y z with
          | inl h_le =>
              have : min y z = y := min_eq_left h_le
              -- it's the middle element
              simp_all [List.minHelper]
          | inr hz_le =>
              have : min y z = z := min_eq_right hz_le
              -- it's the head element
              simp_all [List.minHelper]
      | inr hInYs =>
          -- Already in the tail -> certainly in `z :: y :: ys`
          simp [List.minHelper, List.mem_cons, hInYs]


lemma Problem2 (l : List ℕ) : l.FindMin.MinOfList l := by
  unfold Option.MinOfList
  cases l with
  | nil =>
    simp [List.FindMin]
    -- Here l = []
    -- So FindMin = none
  | cons x xs =>
    simp [List.FindMin]
    constructor
    · -- membership: expect a disjunction form after simp
      -- turn `xs.minHelper x ∈ x :: xs` into `... = x ∨ ... ∈ xs`
      simpa [List.mem_cons] using (minHelper_membership xs x)
    · -- minimality, usually normalized by simp to: ≤ head ∧ ≤ every tail element
      constructor
      · -- ≤ head
        simpa using minHelper_le_acc xs x
      · -- ≤ any element of the tail
        exact minHelper_inf x xs


-- For problem 3 and 4, we will use the following version of Merge and Sorted
-- # Merge
def Merge: List ℕ → List ℕ → List ℕ
  | x, [] => x
  | [], x => x
  | x::xs, y::ys =>
    if x ≤ y then x :: Merge xs (y::ys)
    else y :: Merge (x :: xs) ys

-- # Sorted
inductive Sorted: List ℕ  → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ ) (t : List ℕ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t  → Sorted (t) →  Sorted (a :: t)

-- # Problem 3: Prove that y ∈ Merge xs (y :: ys)
-- You may find this List functions helpful
#check List.mem_cons_of_mem
#check List.mem_cons_self

theorem Problem3 (y : ℕ) (xs ys: List ℕ) : y ∈ Merge xs (y :: ys) := by
  match xs with
  | [] => simp_all [Merge]
  | x::xsr =>
    unfold Merge
    split_ifs
    · have h_y_membership : y ∈ Merge xsr (y :: ys) := by exact Problem3 y xsr ys
      grind [List.mem_cons_of_mem]
    -- expose_names
    -- · simp
    --   by_cases h_xy: x = y
    --   · left
    --     grind
    --   · have h_x_lt_y : x < y := by grind
    --     right
    --     exact Problem3 y xsr ys
    · exact List.mem_cons_self

-- # Problem 4: Prove that Merge function is commutative on sorted inputs
-- `nth_rewrite` tactic can be useful to rewrite a specific occurence
-- You may find this function useful and you may find the API about merge and sorted helpful
#check Merge.eq_def

-- # API about Merge
-- In this homework, let's assume you have access to the following theorems.
-- Proving these theorems are optional.
theorem sorted_suffix {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : Sorted xs := sorry
theorem sorted_min {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) :  x.MinOfList xs  := by sorry
theorem merge_min_out (x : ℕ) (xs ys : List ℕ) (h_min_in_xs : ∀ y ∈ xs, x ≤ y) : Merge (x :: ys) xs = x :: Merge ys xs := by sorry
theorem merge_min_out_sym(x : ℕ) (xs ys : List ℕ) (h_min_in_xs : ∀ y ∈ xs, x ≤ y) (h_min_in_ys : ∀ y ∈ ys, x ≤ y) : Merge ys (x ::xs)  = x :: Merge ys xs := by sorry

#print Nat.MinOfList

theorem Problem4  (xs ys: List ℕ) (h1: Sorted xs) (h2: Sorted ys): Merge xs ys = Merge ys xs := by
  fun_induction Merge xs ys
  . grind [Merge]
  · grind [Merge]

  · have h_x_min_xlist : ∀ x_i ∈ xs_1, x ≤ x_i := by
      rw [← Nat.MinOfList]
      exact sorted_min h1
    have h_y_min_ylist : ∀ y_i ∈ ys_1, y ≤ y_i := by
      rw [← Nat.MinOfList]
      exact sorted_min h2

    apply sorted_suffix at h1
    replace ih1 : Merge xs_1 (y :: ys_1) = Merge (y :: ys_1) xs_1 := by grind
    rw [ih1]
    grind [merge_min_out_sym]

  · simp at h
    replace h : y ≤ x := by omega

    have h_x_min_xlist : ∀ x_i ∈ xs_1, x ≤ x_i := by
      rw [← Nat.MinOfList]
      exact sorted_min h1
    have h_y_min_ylist : ∀ y_i ∈ ys_1, y ≤ y_i := by
      rw [← Nat.MinOfList]
      exact sorted_min h2

    apply sorted_suffix at h2
    replace ih1 : Merge (x :: xs_1) ys_1 = Merge ys_1 (x :: xs_1) := by grind
    rw [ih1]
    grind [merge_min_out]

-- # Problem 5: Prove that the index returned by this contain_bs correctly corresponds to q
-- Consider the following SortedArrayFun and contain_bs function

structure SortedArrayFun (n :ℕ) where
  get : ℕ → ℕ
  size : ℕ := n
  sorted: Monotone get

def contains_bs {n :ℕ }(arr : SortedArrayFun n) (q : ℕ) : Option ℕ :=
  bs_aux 0 (n-1) (by omega)
  where bs_aux (a b :ℕ) (h: a ≤ b): Option ℕ :=
  if h: a = b then
    if q = arr.get a then some a
    else none
  else
    let mid := (a+b)/(2 :ℕ)
    if q < arr.get mid then bs_aux a mid (by omega)
    else if arr.get mid < q then bs_aux (mid+1) b (by omega)
    else some mid

#check contains_bs
#check contains_bs.bs_aux

lemma h_interval (n q a b :ℕ) (arr : SortedArrayFun n) (h_le: a ≤ b)
  : ∀ i, contains_bs.bs_aux arr q a b h_le = some i → arr.get i = q := by
  intro i

  /- # This way shows more details
  by_cases h_case : a = b
  · unfold contains_bs.bs_aux
    simp_all
  · unfold contains_bs.bs_aux
    simp_all
    split_ifs with h1 h2
    · -- Recursive case: search left
      apply h_interval n q a ((a+b)/2) arr (by omega)
    · -- Recursive case: search right
      apply h_interval n q ((a+b)/2+1) b arr (by omega)
    · -- Base case: found it
      set mid := (a + b) / 2 with h_mid_def
      -- # equvalently,
      -- generalize h_mid : (a + b) / 2 = mid
      intro h_mid_eq_i
      have h_mid_q : arr.get mid = q := by grind
      grind
    -/

  fun_induction contains_bs.bs_aux
  · grind
  · grind
  · exact ih1
  · exact ih1
  · have h_mid_q : arr.get mid = q := by grind
    grind
    -- intro h_mid_eq_i
    -- simp only [Option.some.injEq] at h_mid_eq_i
    -- rw [← h_mid_eq_i, h_mid_q]

theorem Problem5 (n q :ℕ)
  (h: 0 < n) (arr : SortedArrayFun n)
  : ∀ i, contains_bs arr q = some i → arr.get i = q := by
  intro i hi
  unfold contains_bs at hi
  grind [h_interval]
