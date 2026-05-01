import D7Odd.Handoff.SmallRootFlat

namespace D7Odd
namespace Handoff

-- Finite selector tables from d7_m3_m5_zero_set_certificates.json.
-- Masks use bit i for membership of coordinate i in the zero-set.

def addMod7 (a b : Fin 7) : Fin 7 :=
  Fin.ofNat 7 (a.val + b.val)

def selector3Mask (mask : Nat) : Fin 7 :=
  match mask with
  | 0 => 3
  | 1 => 6
  | 2 => 6
  | 3 => 4
  | 4 => 5
  | 5 => 1
  | 6 => 4
  | 7 => 1
  | 8 => 3
  | 9 => 2
  | 10 => 0
  | 11 => 0
  | 12 => 1
  | 13 => 2
  | 14 => 1
  | 15 => 6
  | 16 => 6
  | 17 => 3
  | 18 => 5
  | 19 => 4
  | 20 => 0
  | 21 => 0
  | 22 => 4
  | 23 => 6
  | 24 => 1
  | 25 => 3
  | 26 => 1
  | 27 => 2
  | 28 => 0
  | 29 => 0
  | 30 => 6
  | 31 => 2
  | 32 => 6
  | 33 => 1
  | 34 => 3
  | 35 => 1
  | 36 => 5
  | 37 => 3
  | 38 => 4
  | 39 => 4
  | 40 => 0
  | 41 => 0
  | 42 => 3
  | 43 => 2
  | 44 => 1
  | 45 => 3
  | 46 => 1
  | 47 => 2
  | 48 => 6
  | 49 => 1
  | 50 => 5
  | 51 => 1
  | 52 => 0
  | 53 => 0
  | 54 => 4
  | 55 => 4
  | 56 => 0
  | 57 => 0
  | 58 => 6
  | 59 => 6
  | 60 => 6
  | 61 => 1
  | 62 => 6
  | 64 => 3
  | 65 => 6
  | 66 => 6
  | 67 => 2
  | 68 => 0
  | 69 => 0
  | 70 => 3
  | 71 => 2
  | 72 => 3
  | 73 => 5
  | 74 => 5
  | 75 => 4
  | 76 => 4
  | 77 => 5
  | 78 => 3
  | 79 => 6
  | 80 => 6
  | 81 => 3
  | 82 => 5
  | 83 => 5
  | 84 => 5
  | 85 => 5
  | 86 => 5
  | 87 => 6
  | 88 => 1
  | 89 => 3
  | 90 => 1
  | 91 => 4
  | 92 => 4
  | 93 => 1
  | 94 => 6
  | 96 => 6
  | 97 => 4
  | 98 => 0
  | 99 => 0
  | 100 => 3
  | 101 => 1
  | 102 => 3
  | 103 => 1
  | 104 => 4
  | 105 => 5
  | 106 => 5
  | 107 => 2
  | 108 => 3
  | 109 => 5
  | 110 => 3
  | 112 => 6
  | 113 => 4
  | 114 => 5
  | 115 => 5
  | 116 => 5
  | 117 => 5
  | 118 => 5
  | 120 => 4
  | 121 => 2
  | 122 => 6
  | 124 => 6
  | 127 => 3
  | _ => 0

def selector5Mask (mask : Nat) : Fin 7 :=
  match mask with
  | 0 => 4
  | 1 => 3
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 4
  | 9 => 3
  | 10 => 2
  | 11 => 2
  | 12 => 0
  | 13 => 0
  | 14 => 2
  | 15 => 2
  | 16 => 4
  | 17 => 3
  | 18 => 5
  | 19 => 5
  | 20 => 0
  | 21 => 0
  | 22 => 5
  | 23 => 5
  | 24 => 4
  | 25 => 3
  | 26 => 0
  | 27 => 0
  | 28 => 1
  | 29 => 1
  | 30 => 1
  | 31 => 1
  | 32 => 0
  | 33 => 0
  | 34 => 0
  | 35 => 0
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 2
  | 41 => 4
  | 42 => 0
  | 43 => 0
  | 44 => 2
  | 45 => 1
  | 46 => 4
  | 47 => 1
  | 48 => 0
  | 49 => 0
  | 50 => 5
  | 51 => 5
  | 52 => 0
  | 53 => 0
  | 54 => 5
  | 55 => 5
  | 56 => 1
  | 57 => 4
  | 58 => 1
  | 59 => 2
  | 60 => 0
  | 61 => 0
  | 62 => 4
  | 64 => 3
  | 65 => 1
  | 66 => 2
  | 67 => 1
  | 68 => 0
  | 69 => 0
  | 70 => 2
  | 71 => 5
  | 72 => 3
  | 73 => 1
  | 74 => 2
  | 75 => 1
  | 76 => 5
  | 77 => 5
  | 78 => 2
  | 79 => 4
  | 80 => 1
  | 81 => 1
  | 82 => 1
  | 83 => 1
  | 84 => 0
  | 85 => 0
  | 86 => 3
  | 87 => 5
  | 88 => 2
  | 89 => 5
  | 90 => 0
  | 91 => 0
  | 92 => 2
  | 93 => 5
  | 94 => 3
  | 96 => 2
  | 97 => 1
  | 98 => 3
  | 99 => 1
  | 100 => 2
  | 101 => 4
  | 102 => 3
  | 103 => 5
  | 104 => 4
  | 105 => 1
  | 106 => 3
  | 107 => 1
  | 108 => 5
  | 109 => 5
  | 110 => 3
  | 112 => 1
  | 113 => 1
  | 114 => 1
  | 115 => 1
  | 116 => 1
  | 117 => 4
  | 118 => 1
  | 120 => 4
  | 121 => 5
  | 122 => 0
  | 124 => 1
  | 127 => 4
  | _ => 0

def offset3 (t : Fin 3) : Fin 7 :=
  match t.val with
  | 0 => 2
  | 2 => 4
  | _ => 0

def offset5 (t : Fin 5) : Fin 7 :=
  match t.val with
  | 0 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 6
  | _ => 0

def smallDir3 (t : Fin 3) (w : RootState7 3) (c : Fin 7) : Fin 7 :=
  if t.val = 1 then
    addMod7 (selector3Mask (shiftMask7 (zeroMask 3 w) c)) c
  else
    addMod7 c (offset3 t)

def smallDir5 (t : Fin 5) (w : RootState7 5) (c : Fin 7) : Fin 7 :=
  if t.val = 1 then
    addMod7 (selector5Mask (shiftMask7 (zeroMask 5 w) c)) c
  else
    addMod7 c (offset5 t)

def smallLayer3 (t : Fin 3) (c : Fin 7) (w : RootState7 3) : RootState7 3 :=
  addQRoot 3 (smallDir3 t w c) w

def smallLayer5 (t : Fin 5) (c : Fin 7) (w : RootState7 5) : RootState7 5 :=
  addQRoot 5 (smallDir5 t w c) w

def smallReturn3 (c : Fin 7) (w : RootState7 3) : RootState7 3 :=
  smallLayer3 2 c (smallLayer3 1 c (smallLayer3 0 c w))

def smallReturn5 (c : Fin 7) (w : RootState7 5) : RootState7 5 :=
  smallLayer5 4 c (smallLayer5 3 c (smallLayer5 2 c (smallLayer5 1 c (smallLayer5 0 c w))))

def SmallCertificateTarget3 : Prop :=
  (∀ t c, Function.Bijective (smallLayer3 t c)) ∧
    (∀ t w, Function.Bijective fun c : Fin 7 => smallDir3 t w c) ∧
    (∀ c, IsSingleCycleMap (smallReturn3 c))

def SmallCertificateTarget5 : Prop :=
  (∀ t c, Function.Bijective (smallLayer5 t c)) ∧
    (∀ t w, Function.Bijective fun c : Fin 7 => smallDir5 t w c) ∧
    (∀ c, IsSingleCycleMap (smallReturn5 c))

end Handoff
end D7Odd
