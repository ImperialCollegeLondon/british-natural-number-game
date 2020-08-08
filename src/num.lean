import cs

namespace xena


/-- The type of nonnegative binary numbers, using `pos_num`.

     13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one))) -/
@[derive has_reflect, derive decidable_eq]
inductive num : Type
| zero  : num
| pos   : pos_num → num
instance : has_zero num := ⟨num.zero⟩
instance : has_one num := ⟨num.pos 1⟩
instance : inhabited num := ⟨0⟩

/-- Representation of integers using trichotomy around zero.

     13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one)))
     -13 = -1101(base 2) = neg (bit1 (bit0 (bit1 one))) -/
@[derive has_reflect, derive decidable_eq]
inductive znum : Type
| zero : znum
| pos  : pos_num → znum
| neg  : pos_num → znum
instance foo1 : has_zero znum := ⟨znum.zero⟩
instance bar1 : has_one znum := ⟨znum.pos 1⟩
instance baz1 : inhabited znum := ⟨0⟩

/-- See `snum`. -/
@[derive has_reflect, derive decidable_eq]
inductive nzsnum : Type
| msb : bool → nzsnum
| bit : bool → nzsnum → nzsnum
/-- Alternative representation of integers using a sign bit at the end.
  The convention on sign here is to have the argument to `msb` denote
  the sign of the MSB itself, with all higher bits set to the negation
  of this sign. The result is interpreted in two's complement.

     13  = ..0001101(base 2) = nz (bit1 (bit0 (bit1 (msb tt))))
     -13 = ..1110011(base 2) = nz (bit1 (bit1 (bit0 (msb ff))))

  As with `num`, a special case must be added for zero, which has no msb,
  but by two's complement symmetry there is a second special case for -1.
  Here the `bool` field indicates the sign of the number.

     0  = ..0000000(base 2) = zero ff
     -1 = ..1111111(base 2) = zero tt -/
@[derive has_reflect, derive decidable_eq]
inductive snum : Type
| zero : bool → snum
| nz : nzsnum → snum
instance : has_coe nzsnum snum := ⟨snum.nz⟩
instance foo : has_zero snum := ⟨snum.zero ff⟩
instance moo : has_one nzsnum := ⟨nzsnum.msb tt⟩
instance boo : has_one snum := ⟨snum.nz 1⟩
instance  bar : inhabited nzsnum := ⟨1⟩
instance baz : inhabited snum := ⟨0⟩


-- doesn't work for some reason
--   def pred' : pos_num → num
--   | 1        := 0
--   | (bit0 n) := num.pos (num.cases_on (pred' n) 1 bit1)
--   | (bit1 n) := num.pos (bit0 n)

end xena
