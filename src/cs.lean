import pos_num

namespace xena

namespace pos_num

  def bit (b : bool) : ℙ → ℙ := cond b bit1 bit0

  def is_one : ℙ → bool
  | 1 := tt
  | _ := ff


  def nat_size : ℙ → nat
  | 1        := 1
  | (bit0 n) := nat.succ (nat_size n)
  | (bit1 n) := nat.succ (nat_size n)

open ordering

  def cmp : ℙ → ℙ → ordering
  | 1        1        := eq
  | _        1        := gt
  | 1        _        := lt
  | (bit0 a) (bit0 b) := cmp a b
  | (bit0 a) (bit1 b) := ordering.cases_on (cmp a b) lt lt gt
  | (bit1 a) (bit0 b) := ordering.cases_on (cmp a b) lt gt gt
  | (bit1 a) (bit1 b) := cmp a b

end pos_num

end xena
