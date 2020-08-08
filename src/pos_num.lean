-- `pos_num` -- the British Natural Numbers.
-- The same as pnat

import tactic

namespace xena

--import data.vector data.bitvec

/-- The type of positive binary numbers.

     13 = 1101(base 2) = bit1 (bit0 (bit1 one)) -/
@[derive has_reflect, derive decidable_eq]
inductive pos_num : Type
| one  : pos_num
| bit1 : pos_num → pos_num
| bit0 : pos_num → pos_num

notation `ℙ` := pos_num

namespace pos_num

instance : has_one ℙ := ⟨pos_num.one⟩

def thirty_seven := bit1 (bit0 (bit1 (bit0 (bit0 (one)))))

instance : inhabited ℙ := ⟨thirty_seven⟩

--#print pos_num.rec
@[simp] lemma rec_one (C : ℙ → Type) (x : C 1) (h1 : Π (a : ℙ), C a → C (bit1 a))
 (h0 : Π (a : ℙ), C a → C (bit0 a)) : (pos_num.rec x h1 h0 1  : C 1) = x := rfl

@[simp] lemma rec_one' (C : ℙ → Type) (x : C 1) (h1 : Π (a : ℙ), C a → C (bit1 a))
 (h0 : Π (a : ℙ), C a → C (bit0 a)) : (pos_num.rec x h1 h0 one  : C one) = x := rfl

@[simp] lemma rec_bit0 (C : ℙ → Type) (x : C 1) (h1 : Π (a : ℙ), C a → C (bit1 a))
   (h0 : Π (a : ℙ), C a → C (bit0 a)) (p : ℙ) :
   (pos_num.rec x h1 h0 (bit0 p)  : C (bit0 p)) = h0 p (pos_num.rec x h1 h0 p) := rfl

@[simp] lemma rec_bit1 (C : ℙ → Type) (x : C 1) (h1 : Π (a : ℙ), C a → C (bit1 a))
   (h0 : Π (a : ℙ), C a → C (bit0 a)) (p : ℙ) :
   (pos_num.rec x h1 h0 (bit1 p)  : C (bit1 p)) = h1 p (pos_num.rec x h1 h0 p) := rfl


def succ : ℙ → ℙ
| 1        := bit0 one
| (bit1 n) := bit0 (succ n)
| (bit0 n) := bit1 n

@[simp] lemma succ_one : succ 1 = bit0 1 := rfl
@[simp] lemma succ_bit1 (n : ℙ) : succ (bit1 n) = bit0 (succ n) := rfl
@[simp] lemma succ_bit0 (n : ℙ) : succ (bit0 n) = bit1 n := rfl

/-! # Addition -/

-- Working on making mathematician's interface and
-- recursor for addition.

-- computer scientists want this definition
/-- addition on ℙ -/
protected def add : ℙ → ℙ → ℙ
| 1        b        := succ b
| a        1        := succ a
| (bit0 a) (bit0 b) := bit0 (add a b)
| (bit1 a) (bit1 b) := bit0 (succ (add a b))
| (bit0 a) (bit1 b) := bit1 (add a b)
| (bit1 a) (bit0 b) := bit1 (add a b)

-- I don't need succ, I want + to be the primitive object
-- because it has more symmetries
/--
latexdef $ (+) : \P^2 \to \P $
| 1        1        := bit0 1
| 1        (bit0 b) := bit1 b
| 1        (bit1 b) := bit0 (1 + b)
| (bit0 a) 1        := bit1 a
| (bit1 a) 1        := bit1 (a + 1)
| (bit0 a) (bit0 b) := bit0 (a + b)
-- when I do the carry one, in exactly
-- what order do I add the carry 1 to the
-- two digits in the next column?
-- This way is is "add like normal, but then don't forget to add on
-- the carry one after"
| (bit1 a) (bit1 b) := bit0 ((a + b) + 1)
| (bit0 a) (bit1 b) := bit1 (a + b)
| (bit1 a) (bit0 b) := bit1 (a + b)
-/
instance : has_add ℙ := ⟨pos_num.add⟩

/-! # Succ -/


lemma succ_eq_add_one (a : ℙ) : succ a = a + 1 :=
begin
  cases a; refl
end

lemma succ_eq_one_add (a : ℙ) : succ a = 1 + a :=
begin
  cases a; refl
end

/-! # Mathematician's interface to addition -/
-- note: add_succ not yet done

@[simp] lemma one_add_one : 1 + 1 = bit0 1 := rfl
@[simp] lemma one_add_bit0 (p : ℙ) :
  1 + bit0 p = bit1 p := rfl
@[simp] lemma one_add_bit1 (p : ℙ) :
  (1 : ℙ) + (bit1 p) = bit0 (1 + p) :=
  begin
    change succ (bit1 p) = _,
    unfold succ,
    congr,
    apply succ_eq_one_add,
  end  

@[simp] lemma bit0_add_one (a : ℙ) : (bit0 a) + 1 = bit1 a := rfl
@[simp] lemma bit1_add_one (a : ℙ) : (bit1 a) + 1 = bit0 (a + 1) :=
begin
  show succ (bit1 a) = _,
  unfold succ,
  rw succ_eq_add_one
end

@[simp] lemma bit0_add_bit0 (a b : ℙ) :
  (bit0 a) + (bit0 b) = bit0 (a + b) := rfl
@[simp] lemma bit1_add_bit1 (a b : ℙ) :
  (bit1 a) + (bit1 b) = bit0 ((a + b) + 1) :=
begin
--  show (bit1 a) + (bit1 b) = bit0 ((a + b) + 1) :=
  show bit0 (succ (a + b)) = _,
  rw succ_eq_add_one
end

@[simp] lemma bit0_add_bit1 (a b : ℙ) :
 (bit0 a) + (bit1 b) = bit1 (a + b) := rfl
@[simp] lemma bit1_add_bit0 (a b : ℙ) :
  (bit1 a) + (bit0 b) = bit1 (a + b) := rfl


/-! # Even and odd -/

-- This just works.

/-! # Even and odd -- it all works -/
inductive even : ℙ → Prop
| even_bit0 (n : ℙ) : even (bit0 n)

inductive odd : ℙ → Prop
| odd_one : odd 1
| odd_bit1 (n : ℙ) : odd (bit1 n)

def odd_one := odd.odd_one -- put it in the root namespace
def even_bit0 := even.even_bit0
def odd_bit1 := odd.odd_bit1

lemma even_or_odd (a : ℙ) : even a ∨ odd a :=
begin
  cases a,
  right, apply odd_one,
  right, apply odd_bit1,
  left, apply even_bit0
end

lemma not_even_and_odd (a : ℙ) : ¬ (even a ∧ odd a) :=
begin
  induction a,
  { rintro ⟨⟨⟩,_⟩},
  { rintro ⟨⟨⟩,_⟩},
  /-
protected eliminator xena.pos_num.rec : Π {C : ℙ → Sort l},
  C one → (Π (a : ℙ), C a → C (bit1 a)) → (Π (a : ℙ), C a → C (bit0 a)) → Π (n : ℙ), C n
-/

  { rintro ⟨_,⟨⟩⟩ },
end


lemma odd_add_odd (a b : ℙ) (ha : odd a) (hb : odd b) : even (a + b) :=
begin
  cases ha; cases hb; apply even_bit0,
end

lemma odd_add_even (a b : ℙ) (ha : odd a) (hb : even b) : odd (a + b) :=
begin
  cases ha; cases hb; apply odd_bit1,
end

lemma even_add_odd (a b : ℙ) (ha : even a) (hb : odd b) : odd (a + b) :=
begin
  cases ha; cases hb; apply odd_bit1,
end

lemma even_add_even (a b : ℙ) (ha : even a) (hb : even b) : even (a + b) :=
begin
  cases ha; cases hb; apply even_bit0,
end

def equiv.to_fun_aux : ℙ → ℕ :=
pos_num.rec 1 (λ b (n : ℕ), _root_.bit1 n) (λ b n, _root_.bit0 n)

@[simp] lemma equiv.to_fun_aux_one : equiv.to_fun_aux 1 = 1 := rfl
@[simp] lemma equiv.to_fun_aux_one' : equiv.to_fun_aux one = 1 := rfl

@[simp] lemma equiv.to_fun_aux_two : equiv.to_fun_aux (bit0 1) = 2 := rfl

@[simp] lemma equiv.to_fun_aux_bit0 (a : ℙ) : equiv.to_fun_aux (bit0 a) =
  _root_.bit0 (equiv.to_fun_aux a) :=
begin
  refl
end
#print _root_.bit0

@[simp] lemma equiv.to_fun_aux_bit1 (a : ℙ) : equiv.to_fun_aux (bit1 a) =
  (equiv.to_fun_aux a + equiv.to_fun_aux a + 1) :=
begin
  refl
end

lemma equiv.to_fun_aux_ne_zero (p : ℙ) : equiv.to_fun_aux p ≠ 0 :=
begin
  induction p;
  simp [*, _root_.bit0],
end


def equiv.inv_fun_aux : ℕ → ℙ
| 0 := thirty_seven -- unreachable code has been reached
| 1 := 1
| (n + 2) := succ (equiv.inv_fun_aux (n + 1))

--#print prefix equiv.inv_fun

@[simp] lemma equiv.inv_fun_aux_one : equiv.inv_fun_aux 1 = 1 := rfl
@[simp] lemma equiv.inv_fun_succ_succ (n : ℕ) :
  equiv.inv_fun_aux (n + 2) =
    succ (equiv.inv_fun_aux (n + 1)) :=
begin
  refl
end

@[simp] lemma equiv.inv_map_add (a b : ℕ) :
  equiv.inv_fun_aux (a + b) = equiv.inv_fun_aux a + equiv.inv_fun_aux b :=
begin
  sorry
end


-- equiv.inv_fun_aux : ℕ → pos_num is the identity on positive n.
-- it's defined by recursion



section equiv

/-! # Equiv - an unfinished project. -/

-- the sorries up to the end of this section 
-- this sorry is me being stuck trying to
-- prove that inv_fun commutes with bit1.
-- Shing suggested
/-
probably. I just followed the proof that the Coq people used to see 
what it's like. Their proof is like 7 lines, but I'm not familiar 
enough with Coq (nor do I have it installed) to see what automation 
they're using
and for the lemma you're proving, can you prove 
equiv.inv_fun_aux (a + b) = equiv.inv_fun_aux a + equiv.inv_fun_aux b 
and bit1 x = x + x + 1? If so, then it's easy
then the bit0 case just needs the proof that
 bit0 x = x + x and should be very similar
-/

-- there are two sorries in this section.

lemma equiv.inv_fun_aux_bit1 {n : ℕ} (hn : n ≠ 0) :
  bit1 (equiv.inv_fun_aux n) = equiv.inv_fun_aux (n + n + 1) :=
begin
  cases n with n, cases (hn rfl), clear hn,
  apply nat.strong_induction_on n,
  clear n,
  intros n hn,
  sorry
end


def equiv : ℙ ≃ {n : ℕ // n ≠ 0} :=
{ to_fun := λ p, ⟨equiv.to_fun_aux p, equiv.to_fun_aux_ne_zero p⟩,
  inv_fun := λ n, equiv.inv_fun_aux n.1,
  left_inv := begin
    intro p,
    induction p with p h p h,
    { refl },
    { simp at h,
      simp,
      conv begin to_rhs, rw ←h, end,
      suffices : equiv.inv_fun_aux (_root_.bit1 (equiv.to_fun_aux p)) = 
      bit1 (equiv.inv_fun_aux (equiv.to_fun_aux p)),
        convert this,
        sorry,
      sorry },
    { sorry }
  end,
  right_inv := sorry }

end equiv -- now sorry-free again

section pred

/-! # Pred == a possibly mad project. -/

-- I get stuck proving the equiv. There is a sorry in the
-- equiv in this section.

/-! to_fun is the bijection ℙ → ℕ, considered as a function. -/
def pred.to_fun : ℙ → ℕ :=
pos_num.rec 0 (λ b (n : ℕ), (n + n + 1 + 1)) (λ b n, n + n + 1)

-- interface for pred.to_fun
lemma pred.to_fun_one : pred.to_fun 1 = 0 := rfl
lemma pred.to_fun_two : pred.to_fun (bit0 1) = 1 := rfl
lemma pred.to_fun_bit0 (a : ℙ) : pred.to_fun (bit0 a) =
  (pred.to_fun a) + (pred.to_fun a) + 1 :=
begin
  refl
end

lemma pred.to_fun_bit1 (a : ℙ) : pred.to_fun (bit1 a) =
  (pred.to_fun a + pred.to_fun a + 1 + 1) :=
begin
  refl
end

/-- `inv_fun : the bijection ℕ → ℙ, considered as a function -/
def pred.inv_fun := nat.rec 1 (λ n p, succ p)

-- the interface for inv_fun

lemma pred.inv_fun_zero : pred.inv_fun 0 = 1 :=rfl
lemma pred.inv_fun_succ (n : ℕ) :
  pred.inv_fun (nat.succ n) = succ (pred.inv_fun n) :=rfl
lemma pred.inv_fun_succ' (n : ℕ) :
  pred.inv_fun (n + 1) = succ (pred.inv_fun n) :=rfl


-- there is a sorry in the def of the equiv

/-! # equiv -/
def pred : ℙ ≃ ℕ :=
{ to_fun := pred.to_fun,
  inv_fun := pred.inv_fun,
  left_inv := begin
    intro p,
    induction p with p hp p hp,
    { refl },
    { rw pred.to_fun_bit1,
      rw pred.inv_fun_succ',
      simp,
--      simp_rw [pos_num.rec_bit1],
--      let ZZZ := @nat.rec _ 1 (λ (n : ℕ), succ)
--      (pos_num.rec 0 (λ (b : ℙ) (n : ℕ), n + n) (λ (b : ℙ) (n : ℕ), n + n + 1) (bit1 n_a)) = bit1 n_a,
--      change ZZZ,
      -- change @nat.rec _ 1 (λ (n : ℕ), succ)
      -- (pos_num.rec
      --   0
      --   (λ (b : ℙ) (n : ℕ), n + n)
      --   (λ (b : ℙ) (n : ℕ), n + n + 1)
      --   (bit1 n_a)
      -- ) = bit1 n_a,
      -- let WWW := @nat.rec _ 1 (λ (n : ℕ), succ)
      -- ((pos_num.rec
      --   0
      --   (λ (b : ℙ) (n : ℕ), n + n)
      --   (λ (b : ℙ) (n : ℕ), n + n + 1)
      --   n_a
      -- ) +
      --      (pos_num.rec
      --   0
      --   (λ (b : ℙ) (n : ℕ), n + n)
      --   (λ (b : ℙ) (n : ℕ), n + n + 1)
      --   n_a
      -- ) +
      -- 1)
      -- = bit1 n_a,
      -- suffices : WWW,
      -- convert this,
      
      sorry,
       },
    { sorry }
  end,
  right_inv := sorry }

-- the above section is a WIP
end pred





/-! # Open Succ project -/

lemma add_succ (a b : ℙ) : a + succ b = succ (a + b) :=
begin
  induction a; induction b;
  try {refl },
  repeat {sorry },
end

/-! # Addition -/

-- I got stuck proving it was a semigroup.
-- I want to deduce this from after the equiv
-- so I should fix the equiv first

lemma add_assoc (a b c : ℙ) : a + (b + c) = (a + b) + c :=
begin
  induction c,

  repeat {sorry},
end

/-! # The usual induction principle -/

-- Should I deduce this from an equiv to a nat-like object?
lemma induction (C : ℙ → Prop) (h1 : C 1) (hsucc : ∀ n : ℙ, C n → C (n + 1)) :
  ∀ n, C n :=
begin
  intro n,
  induction n with a b,
  { assumption },
  repeat {sorry},
end



def pred' : ℙ → ℙ
| 1 := 37
| (bit1 a) := bit0 a
| (bit0 a) := bit1 (pred' a)

def size : ℙ → ℙ
| 1        := 1
| (bit0 n) := succ (size n)
| (bit1 n) := succ (size n)


  protected def mul (a : ℙ) : ℙ → ℙ
  | 1        := a
  | (bit0 b) := bit0 (mul b)
  | (bit1 b) := bit0 (mul b) + a

  instance : has_mul ℙ := ⟨pos_num.mul⟩

  def of_nat_succ : ℕ → ℙ
  | 0            := 1
  | (nat.succ n) := succ (of_nat_succ n)

  def of_nat (n : ℕ) : ℙ := of_nat_succ (nat.pred n)

/-! # semigroup-/




  open ordering

-- inductive prop
-- not sure if this is right
inductive le : ∀ (a b : ℙ), Prop
| one_le : ∀ (a : ℙ), le 1 a 
| bit0_mono : ∀ (a b : ℙ), le a b → le (bit0 a) (bit0 b)
| bit1_mono : ∀ (a b : ℙ), le a b → le (bit1 a) (bit1 b)
| comm_diag : ∀ (a b : ℙ), le a b → le (bit0 a) (bit1 b)  
| funny_one : ∀ (a b : ℙ), le a b → a ≠ b → le (bit1 a) (bit0 b)

namespace le

instance : has_le ℙ := ⟨le⟩

--has_lt will be autogenerated by preorder

instance : partial_order ℙ :=
{ le := (≤),
  le_refl := begin
    intro a,
    induction a,
    apply one_le,
    apply bit1_mono,
    assumption,
    apply bit0_mono,
    assumption,
  end,
  le_trans := begin
    rintros a b c hab hbc,
    induction hab with B B C hBC bCBc b6 b7 b8 b9 b10;
    clear a b,
    -- with b | ⟨a, b, hab⟩ | ⟨a, b, hab⟩ | ⟨a,
 --b, hab⟩ | ⟨a, b, hab, haneb⟩,
    { apply one_le },
    { rcases hbc with hab,
      apply bit0_mono,
      cases hbc with hbc,
--      cases hbc,
--      apply bit0_mono,
--      assumption,
--      cases c,
--      { cases hbc },
      { sorry },
      { sorry }},

    -- rintros ⟨_,a0,a1⟩ ⟨_,b0,b1⟩ ⟨_,c0,c1⟩,
    -- --try {cc}, -- solves five of them
    -- { cc },
    -- { cc },
    -- { cc },
    -- { intros, apply one_le one,

    -- },

    sorry, sorry, sorry
  end,
  le_antisymm := begin
    sorry
  end }

end le

end pos_num

end xena

#exit

--instance : has_lt ℙ := ⟨λa b, cmp a b = ordering.lt⟩

theorem le_refl (a : ℙ) : a ≤ a := sorry


#exit

instance : has_lt ℙ := ⟨λa b, cmp a b = ordering.lt⟩
instance : has_le ℙ := ⟨λa b, ¬ b < a⟩

  instance decidable_lt : @decidable_rel ℙ (<)
  | a b := by dsimp [(<)]; apply_instance

  instance decidable_le : @decidable_rel ℙ (≤)
  | a b := by dsimp [(≤)]; apply_instance

end ℙ

section
  variables {α : Type*} [has_zero α] [has_one α] [has_add α]

  def cast_pos_num : ℙ → α
  | 1                := 1
  | (ℙ.bit0 a) := bit0 (cast_pos_num a)
  | (ℙ.bit1 a) := bit1 (cast_pos_num a)

  def cast_num : num → α
  | 0           := 0
  | (num.pos p) := cast_pos_num p

  @[priority 10] instance pos_num_coe : has_coe ℙ α := ⟨cast_pos_num⟩

  @[priority 10] instance num_nat_coe : has_coe num α := ⟨cast_num⟩

  instance : has_repr ℙ := ⟨λ n, repr (n : ℕ)⟩
  instance : has_repr num := ⟨λ n, repr (n : ℕ)⟩
end

namespace num
  open ℙ

  def succ' : num → ℙ
  | 0       := 1
  | (pos p) := succ p

  def succ (n : num) : num := pos (succ' n)

  protected def add : num → num → num
  | 0       a       := a
  | b       0       := b
  | (pos a) (pos b) := pos (a + b)

  instance : has_add num := ⟨num.add⟩

  protected def bit0 : num → num
  | 0       := 0
  | (pos n) := pos (ℙ.bit0 n)

  protected def bit1 : num → num
  | 0       := 1
  | (pos n) := pos (ℙ.bit1 n)

  def bit (b : bool) : num → num := cond b num.bit1 num.bit0

  def size : num → num
  | 0       := 0
  | (pos n) := pos (ℙ.size n)

  def nat_size : num → nat
  | 0       := 0
  | (pos n) := ℙ.nat_size n

  protected def mul : num → num → num
  | 0       _       := 0
  | _       0       := 0
  | (pos a) (pos b) := pos (a * b)

  instance : has_mul num := ⟨num.mul⟩

  open ordering
  def cmp : num → num → ordering
  | 0       0       := eq
  | _       0       := gt
  | 0       _       := lt
  | (pos a) (pos b) := ℙ.cmp a b

  instance : has_lt num := ⟨λa b, cmp a b = ordering.lt⟩
  instance : has_le num := ⟨λa b, ¬ b < a⟩

  instance decidable_lt : @decidable_rel num (<)
  | a b := by dsimp [(<)]; apply_instance

  instance decidable_le : @decidable_rel num (≤)
  | a b := by dsimp [(≤)]; apply_instance

  def to_znum : num → znum
  | 0       := 0
  | (pos a) := znum.pos a

  def to_znum_neg : num → znum
  | 0       := 0
  | (pos a) := znum.neg a

  def of_nat' : ℕ → num :=
  nat.binary_rec 0 (λ b n, cond b num.bit1 num.bit0)

end num

namespace znum
  open ℙ

  def zneg : znum → znum
  | 0       := 0
  | (pos a) := neg a
  | (neg a) := pos a

  instance : has_neg znum := ⟨zneg⟩

  def abs : znum → num
  | 0       := 0
  | (pos a) := num.pos a
  | (neg a) := num.pos a

  def succ : znum → znum
  | 0       := 1
  | (pos a) := pos (ℙ.succ a)
  | (neg a) := (ℙ.pred' a).to_znum_neg

  def pred : znum → znum
  | 0       := neg 1
  | (pos a) := (ℙ.pred' a).to_znum
  | (neg a) := neg (ℙ.succ a)

  protected def bit0 : znum → znum
  | 0       := 0
  | (pos n) := pos (ℙ.bit0 n)
  | (neg n) := neg (ℙ.bit0 n)

  protected def bit1 : znum → znum
  | 0       := 1
  | (pos n) := pos (ℙ.bit1 n)
  | (neg n) := neg (num.cases_on (pred' n) 1 ℙ.bit1)

  protected def bitm1 : znum → znum
  | 0       := neg 1
  | (pos n) := pos (num.cases_on (pred' n) 1 ℙ.bit1)
  | (neg n) := neg (ℙ.bit1 n)

  def of_int' : ℤ → znum
  | (n : ℕ) := num.to_znum (num.of_nat' n)
  | -[1+ n] := num.to_znum_neg (num.of_nat' (n+1))

end znum

namespace ℙ
  open znum

  def sub' : ℙ → ℙ → znum
  | a        1        := (pred' a).to_znum
  | 1        b        := (pred' b).to_znum_neg
  | (bit0 a) (bit0 b) := (sub' a b).bit0
  | (bit0 a) (bit1 b) := (sub' a b).bitm1
  | (bit1 a) (bit0 b) := (sub' a b).bit1
  | (bit1 a) (bit1 b) := (sub' a b).bit0

  def of_znum' : znum → option ℙ
  | (znum.pos p) := some p
  | _            := none

  def of_znum : znum → ℙ
  | (znum.pos p) := p
  | _            := 1

  protected def sub (a b : ℙ) : ℙ :=
  match sub' a b with
  | (znum.pos p) := p
  | _ := 1
  end

  instance : has_sub ℙ := ⟨pos_num.sub⟩
end ℙ

namespace num
  def ppred : num → option num
  | 0       := none
  | (pos p) := some p.pred'

  def pred : num → num
  | 0       := 0
  | (pos p) := p.pred'

  def div2 : num → num
  | 0 := 0
  | 1 := 0
  | (pos (ℙ.bit0 p)) := pos p
  | (pos (ℙ.bit1 p)) := pos p

  def of_znum' : znum → option num
  | 0            := some 0
  | (znum.pos p) := some (pos p)
  | (znum.neg p) := none

  def of_znum : znum → num
  | (znum.pos p) := pos p
  | _            := 0

  def sub' : num → num → znum
  | 0       0       := 0
  | (pos a) 0       := znum.pos a
  | 0       (pos b) := znum.neg b
  | (pos a) (pos b) := a.sub' b

  def psub (a b : num) : option num :=
  of_znum' (sub' a b)

  protected def sub (a b : num) : num :=
  of_znum (sub' a b)

  instance : has_sub num := ⟨num.sub⟩
end num

namespace znum
  open ℙ

  protected def add : znum → znum → znum
  | 0       a       := a
  | b       0       := b
  | (pos a) (pos b) := pos (a + b)
  | (pos a) (neg b) := sub' a b
  | (neg a) (pos b) := sub' b a
  | (neg a) (neg b) := neg (a + b)

  instance : has_add znum := ⟨znum.add⟩

  protected def mul : znum → znum → znum
  | 0       a       := 0
  | b       0       := 0
  | (pos a) (pos b) := pos (a * b)
  | (pos a) (neg b) := neg (a * b)
  | (neg a) (pos b) := neg (a * b)
  | (neg a) (neg b) := pos (a * b)

  instance : has_mul znum := ⟨znum.mul⟩

  open ordering
  def cmp : znum → znum → ordering
  | 0       0       := eq
  | (pos a) (pos b) := ℙ.cmp a b
  | (neg a) (neg b) := ℙ.cmp b a
  | (pos _) _       := gt
  | (neg _) _       := lt
  | _       (pos _) := lt
  | _       (neg _) := gt

  instance : has_lt znum := ⟨λa b, cmp a b = ordering.lt⟩
  instance : has_le znum := ⟨λa b, ¬ b < a⟩

  instance decidable_lt : @decidable_rel znum (<)
  | a b := by dsimp [(<)]; apply_instance

  instance decidable_le : @decidable_rel znum (≤)
  | a b := by dsimp [(≤)]; apply_instance

end znum

namespace ℙ

  def divmod_aux (d : ℙ) (q r : num) : num × num :=
  match num.of_znum' (num.sub' r (num.pos d)) with
  | some r' := (num.bit1 q, r')
  | none    := (num.bit0 q, r)
  end

  def divmod (d : ℙ) : ℙ → num × num
  | (bit0 n) := let (q, r₁) := divmod n in
    divmod_aux d q (num.bit0 r₁)
  | (bit1 n) := let (q, r₁) := divmod n in
    divmod_aux d q (num.bit1 r₁)
  | 1        := divmod_aux d 0 1

  def div' (n d : ℙ) : num := (divmod d n).1

  def mod' (n d : ℙ) : num := (divmod d n).2

  def sqrt_aux1 (b : ℙ) (r n : num) : num × num :=
  match num.of_znum' (n.sub' (r + num.pos b)) with
  | some n' := (r.div2 + num.pos b, n')
  | none := (r.div2, n)
  end

  def sqrt_aux : ℙ → num → num → num
  | b@(bit0 b') r n := let (r', n') := sqrt_aux1 b r n in sqrt_aux b' r' n'
  | b@(bit1 b') r n := let (r', n') := sqrt_aux1 b r n in sqrt_aux b' r' n'
  | 1           r n := (sqrt_aux1 1 r n).1
/-

def sqrt_aux : ℕ → ℕ → ℕ → ℕ
| b r n := if b0 : b = 0 then r else
  let b' := shiftr b 2 in
  have b' < b, from sqrt_aux_dec b0,
  match (n - (r + b : ℕ) : ℤ) with
  | (n' : ℕ) := sqrt_aux b' (div2 r + b) n'
  | _ := sqrt_aux b' (div2 r) n
  end

/-- `sqrt n` is the square root of a natural number `n`. If `n` is not a
  perfect square, it returns the largest `k:ℕ` such that `k*k ≤ n`. -/
def sqrt (n : ℕ) : ℕ :=
match size n with
| 0      := 0
| succ s := sqrt_aux (shiftl 1 (bit0 (div2 s))) 0 n
end
-/

end ℙ

namespace num

  def div : num → num → num
  | 0       _       := 0
  | _       0       := 0
  | (pos n) (pos d) := ℙ.div' n d

  def mod : num → num → num
  | 0       _       := 0
  | n       0       := n
  | (pos n) (pos d) := ℙ.mod' n d

  instance : has_div num := ⟨num.div⟩
  instance : has_mod num := ⟨num.mod⟩

  def gcd_aux : nat → num → num → num
  | 0            a b := b
  | (nat.succ n) 0 b := b
  | (nat.succ n) a b := gcd_aux n (b % a) a

  def gcd (a b : num) : num :=
  if a ≤ b then
    gcd_aux (a.nat_size + b.nat_size) a b
  else
    gcd_aux (b.nat_size + a.nat_size) b a

end num

namespace znum

  def div : znum → znum → znum
  | 0       _       := 0
  | _       0       := 0
  | (pos n) (pos d) := num.to_znum (ℙ.div' n d)
  | (pos n) (neg d) := num.to_znum_neg (ℙ.div' n d)
  | (neg n) (pos d) := neg (ℙ.pred' n / num.pos d).succ'
  | (neg n) (neg d) := pos (ℙ.pred' n / num.pos d).succ'

  def mod : znum → znum → znum
  | 0       d := 0
  | (pos n) d := num.to_znum (num.pos n % d.abs)
  | (neg n) d := d.abs.sub' (ℙ.pred' n % d.abs).succ

  instance : has_div znum := ⟨znum.div⟩
  instance : has_mod znum := ⟨znum.mod⟩

  def gcd (a b : znum) : num := a.abs.gcd b.abs

end znum

section
  variables {α : Type*} [has_zero α] [has_one α] [has_add α] [has_neg α]

  def cast_znum : znum → α
  | 0            := 0
  | (znum.pos p) := p
  | (znum.neg p) := -p

  @[priority 10] instance znum_coe : has_coe znum α := ⟨cast_znum⟩

  instance : has_repr znum := ⟨λ n, repr (n : ℤ)⟩
end

/- The snum representation uses a bit string, essentially a list of 0 (ff) and 1 (tt) bits,
   and the negation of the MSB is sign-extended to all higher bits. -/
namespace nzsnum
  notation a :: b := bit a b

  def sign : nzsnum → bool
  | (msb b) := bnot b
  | (b :: p) := sign p

  @[pattern] def not : nzsnum → nzsnum
  | (msb b) := msb (bnot b)
  | (b :: p) := bnot b :: not p
  prefix ~ := not

  def bit0 : nzsnum → nzsnum := bit ff
  def bit1 : nzsnum → nzsnum := bit tt

  def head : nzsnum → bool
  | (msb b)  := b
  | (b :: p) := b

  def tail : nzsnum → snum
  | (msb b)  := snum.zero (bnot b)
  | (b :: p) := p

end nzsnum

namespace snum
  open nzsnum

  def sign : snum → bool
  | (zero z) := z
  | (nz p)   := p.sign

  @[pattern] def not : snum → snum
  | (zero z) := zero (bnot z)
  | (nz p)   := ~p
  prefix ~ := not

  @[pattern] def bit : bool → snum → snum
  | b (zero z) := if b = z then zero b else msb b
  | b (nz p)   := p.bit b

  notation a :: b := bit a b

  def bit0 : snum → snum := bit ff
  def bit1 : snum → snum := bit tt

  theorem bit_zero (b) : b :: zero b = zero b := by cases b; refl

  theorem bit_one (b) : b :: zero (bnot b) = msb b := by cases b; refl

end snum

namespace nzsnum
  open snum

  def drec' {C : snum → Sort*} (z : Π b, C (snum.zero b))
    (s : Π b p, C p → C (b :: p)) : Π p : nzsnum, C p
  | (msb b)  := by rw ←bit_one; exact s b (snum.zero (bnot b)) (z (bnot b))
  | (bit b p) := s b p (drec' p)
end nzsnum

namespace snum
  open nzsnum

  def head : snum → bool
  | (zero z) := z
  | (nz p)   := p.head

  def tail : snum → snum
  | (zero z) := zero z
  | (nz p)   := p.tail

  def drec' {C : snum → Sort*} (z : Π b, C (snum.zero b))
    (s : Π b p, C p → C (b :: p)) : Π p, C p
  | (zero b) := z b
  | (nz p)   := p.drec' z s

  def rec' {α} (z : bool → α) (s : bool → snum → α → α) : snum → α :=
  drec' z s

  def bits : snum → Π n, vector bool n
  | p 0     := vector.nil
  | p (n+1) := head p :: bits (tail p) n

  def test_bit : nat → snum → bool
  | 0     p := head p
  | (n+1) p := test_bit n (tail p)

  def succ : snum → snum :=
  rec' (λ b, cond b 0 1) (λb p succp, cond b (ff :: succp) (tt :: p))

  def pred : snum → snum :=
  rec' (λ b, cond b (~1) ~0) (λb p predp, cond b (ff :: p) (tt :: predp))

  protected def neg (n : snum) : snum := succ ~n

  instance : has_neg snum := ⟨snum.neg⟩

  -- First bit is 0 or 1 (tt), second bit is 0 or -1 (tt)
  def czadd : bool → bool → snum → snum
  | ff ff p := p
  | ff tt p := pred p
  | tt ff p := succ p
  | tt tt p := p

  def cadd : snum → snum → bool → snum :=
  rec' (λ a p c, czadd c a p) $ λa p IH,
  rec' (λb c, czadd c b (a :: p)) $ λb q _ c,
  bitvec.xor3 a b c :: IH q (bitvec.carry a b c)

  protected def add (a b : snum) : snum := cadd a b ff

  instance : has_add snum := ⟨snum.add⟩

  protected def sub (a b : snum) : snum := a + -b

  instance : has_sub snum := ⟨snum.sub⟩

  protected def mul (a : snum) : snum → snum :=
  rec' (λ b, cond b (-a) 0) $ λb q IH,
  cond b (bit0 IH + a) (bit0 IH)

  instance : has_mul snum := ⟨snum.mul⟩

end snum

namespace int
  def of_snum : snum → ℤ :=
  snum.rec' (λ a, cond a (-1) 0) (λa p IH, cond a (bit1 IH) (bit0 IH))

  instance snum_coe : has_coe snum ℤ := ⟨of_snum⟩
end int

instance : has_lt snum := ⟨λa b, (a : ℤ) < b⟩
instance : has_le snum := ⟨λa b, (a : ℤ) ≤ b⟩
