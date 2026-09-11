-- STATUS: main-path
import TorusEven.Entry.Seed.SmallCertificate

namespace TorusEven.Entry.Seed

private def twoPairOrder : Equiv.Perm (Fin 8) where
  toFun := ![0, 3, 1, 6, 4, 7, 2, 5]
  invFun := ![0, 2, 6, 1, 4, 7, 3, 5]
  left_inv := by decide
  right_inv := by decide

def smallTwo : SmallCertificate 2 (by decide) where
  root := ![![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0]]
  next := ![![0, 7, 5, 5, 2, 0, 0, 0],
    ![0, 6, 2, 6, 1, 2, 0, 1],
    ![0, 4, 5, 5, 5, 0, 0, 4]]
  rank := ![![0, 2, 2, 2, 3, 1, 1, 1],
    ![0, 2, 0, 2, 3, 1, 1, 3],
    ![0, 3, 2, 2, 2, 1, 1, 3]]
  row := ![![(0, 0), (2, 0), (1, 2), (1, 3), (0, 0), (1, 1), (1, 0), (2, 1)],
    ![(0, 0), (2, 1), (0, 0), (1, 1), (0, 1), (1, 0), (1, 2), (0, 0)],
    ![(0, 0), (1, 0), (2, 0), (2, 1), (2, 0), (0, 0), (0, 0), (1, 0)]]
  pair := (numberedPairs 2).trans twoPairOrder
  descent := by decide
  paired := by decide

private def threePairOrder : Equiv.Perm (Fin 10) where
  toFun := ![0, 3, 5, 9, 1, 7, 4, 8, 2, 6]
  invFun := ![0, 4, 8, 1, 6, 2, 9, 5, 7, 3]
  left_inv := by decide
  right_inv := by decide

def smallThree : SmallCertificate 3 (by decide) where
  root := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 2, 0, 1, 0, 2, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
  next := ![![0, 7, 7, 7, 9, 0, 0, 0, 0, 0],
    ![0, 1, 2, 5, 1, 0, 2, 1, 1, 0],
    ![0, 4, 5, 5, 5, 0, 0, 0, 4, 4]]
  rank := ![![0, 2, 2, 2, 2, 1, 1, 1, 1, 1],
    ![0, 0, 0, 2, 1, 1, 1, 1, 1, 1],
    ![0, 3, 2, 2, 2, 1, 1, 1, 3, 3]]
  row := ![![(0, 0), (2, 0), (1, 2), (1, 3), (0, 0), (1, 0), (1, 1), (1, 0), (2, 1), (2, 1)],
    ![(0, 0), (0, 0), (0, 0), (1, 1), (0, 1), (1, 2), (1, 0), (2, 1), (0, 0), (2, 0)],
    ![(0, 0), (1, 0), (2, 0), (2, 1), (2, 0), (0, 0), (0, 0), (0, 0), (1, 0), (1, 0)]]
  pair := (numberedPairs 3).trans threePairOrder
  descent := by decide
  paired := by decide

end TorusEven.Entry.Seed
