import D7Odd.Cayley
import D7Odd.Handoff.Additive4Plus2

namespace D7Odd
namespace Handoff
namespace Additive4Plus2

theorem ProductRootCertificate.toTorusHamiltonDecompositionD7
    {m : Nat} [NeZero m] (cert : ProductRootCertificate m) :
    D7Odd.TorusHamiltonDecompositionD7 m :=
  D7Odd.torusHamiltonDecompositionD7_of_handoff
    cert.toHamiltonDecompositionD7

theorem ProductRootCertificate.toCayleyHamiltonDecompositionD7
    {m : Nat} [NeZero m] (cert : ProductRootCertificate m) :
    D7Odd.CayleyHamiltonDecompositionD7 m :=
  D7Odd.cayleyHamiltonDecomposition_of_torus
    cert.toTorusHamiltonDecompositionD7

theorem ProductRootCertificate.toSharedCayleyHamiltonDecomposition
    {m : Nat} [NeZero m] (cert : ProductRootCertificate m) :
    Shared.CayleyHamiltonDecomposition 7 m :=
  D7Odd.sharedCayleyHamiltonDecomposition_of_cayley
    cert.toCayleyHamiltonDecompositionD7

end Additive4Plus2
end Handoff
end D7Odd
