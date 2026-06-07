import EvenV11.LowD5M4H2PaperRow

/-!
# Hard slot H2: D5(4) reset-port ribbon rows

`LowD5M4Realization` already contains a detailed hierarchy of D5(4) reset-port
interfaces.  This file exposes the hardest useful entry points in one place and
connects them to the six-obligation v28 checklist.

The legacy paper-table route is kept here as an explicit checkpoint: a
`ResetPortH2PaperCertificateData` (or the slightly weaker
`ResetPortH2PaperTableData`) would be enough after proving:

1. the reset table avoidance facts, already closed by `D54ResetData`;
2. the RF2 skew-product data for the reset-port row family;
3. the prefix-path goals for the pre-final and final-carry layers;
4. the last-layer row-word read goals.

The current H2 pass should not rely on this route as the main target: the broad
last-layer read package is known to be overstrong in `D5M4H2PaperRows`.  The
preferred handoff is the path/core-tail route exposed in `D5M4H2Skeleton`.
Everything below remains useful bookkeeping for regression and comparison.
-/

namespace EvenV11
namespace V28Hard
namespace D5M4RibbonRows

open Shared
open LowD5M4Structural
open LowD5M4Realization
open LowD5M4H2PaperRow

abbrev RibbonData := ResetPortH2RowEquivRibbonRealizationData
abbrev PaperTableData := LowD5M4Realization.ResetPortH2PaperTableData
abbrev PaperCertificateData := LowD5M4Realization.ResetPortH2PaperCertificateData

/-- The concrete H2 table obligation in the most useful paper-facing form: a
base row, RF2 as skew-product layer data, and the paper prefix/read tables. -/
structure H2PaperTableInput where
  data : PaperTableData

/-- Stronger H2 obligation including the audited reset-table certificate.  This
is the form closest to the manuscript's reset paragraph. -/
structure H2PaperCertificateInput where
  data : PaperCertificateData

/-- Forget the reset-table certificate down to the table data consumed by the
current proof spine. -/
def paperTableInput_of_certificateInput
    (input : H2PaperCertificateInput) : H2PaperTableInput where
  data := LowD5M4Realization.resetPortH2SkewProductPrefixTableData_of_paperCertificateData
    input.data

/-- H2 table data produces the current row-equivalence/ribbon handoff. -/
def ribbonData_of_paperTableInput
    (input : H2PaperTableInput) : RibbonData :=
  LowD5M4H2PaperRow.rowEquivRibbonRealizationData_of_paperTableData
    input.data

/-- H2 certificate data produces the current row-equivalence/ribbon handoff. -/
def ribbonData_of_paperCertificateInput
    (input : H2PaperCertificateInput) : RibbonData :=
  ribbonData_of_paperTableInput
    (paperTableInput_of_certificateInput input)

/-- Nonempty form matching `V28PaperInterface.D5M4ParityResetInput`. -/
theorem nonemptyRibbonData_of_paperTableInput
    (input : H2PaperTableInput) : Nonempty RibbonData :=
  ⟨ribbonData_of_paperTableInput input⟩

/-- Nonempty form matching `V28PaperInterface.D5M4ParityResetInput`, starting
from the stronger reset-table certificate package. -/
theorem nonemptyRibbonData_of_paperCertificateInput
    (input : H2PaperCertificateInput) : Nonempty RibbonData :=
  ⟨ribbonData_of_paperCertificateInput input⟩

/-- Direct low-base root-flat family from paper table data. -/
theorem lowD5M4RootFlatFamily_of_paperTableInput
    (input : H2PaperTableInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  LowD5M4H2PaperRow.finalLowD5M4RootFlatCertificateFamily_of_paperTableData
    input.data

/-- Direct low-base root-flat family from paper certificate data. -/
theorem lowD5M4RootFlatFamily_of_paperCertificateInput
    (input : H2PaperCertificateInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  lowD5M4RootFlatFamily_of_paperTableInput
    (paperTableInput_of_certificateInput input)

/-- Drop-in replacement for `EvenV11.assume_lowD5M4RibbonRealizationData` after
one supplies a paper table. -/
theorem candidate_assume_lowD5M4RibbonRealizationData_of_paperTable
    (input : H2PaperTableInput) :
    Nonempty RibbonData :=
  nonemptyRibbonData_of_paperTableInput input

/-- Drop-in replacement for `EvenV11.assume_lowD5M4RibbonRealizationData` after
one supplies the stronger paper certificate. -/
theorem candidate_assume_lowD5M4RibbonRealizationData_of_paperCertificate
    (input : H2PaperCertificateInput) :
    Nonempty RibbonData :=
  nonemptyRibbonData_of_paperCertificateInput input

/-!
## Row-level subgoals to attack next

The following aliases give paper-oriented names to the existing low-level H2
goals.  They let the reset proof be split across RF2, prefix paths, row-word
reads, and final assembly.
-/

/-- RF2 layer-bijectivity in the paper's skew-product form. -/
abbrev RF2SkewProductData
    (baseRow : ResetPortBaseRow) :=
  ResetPortLayerSkewProductData baseRow

/-- The two prefix-path tables, before expanding them to split goals. -/
abbrev PrefixPathTable
    (baseRow : ResetPortBaseRow) : Prop :=
  ResetPortFullPaperPrefixGoals baseRow

/-- The last-layer row-word read table. -/
abbrev RowWordReadTable
    (baseRow : ResetPortBaseRow) : Prop :=
  ResetPortFullPaperRowWordReadGoals baseRow

/-- Assemble the three independent H2 proof artifacts into `PaperTableData`. -/
def paperTableInput_of_rf2_prefix_read
    (baseRow : ResetPortBaseRow)
    (rf2 : RF2SkewProductData baseRow)
    (prefixTable : PrefixPathTable baseRow)
    (read : RowWordReadTable baseRow) :
    H2PaperTableInput where
  data :=
    LowD5M4Realization.resetPortH2PaperTableData_of_prefixReadFields
      baseRow rf2 prefixTable read

/-- The same assembly followed immediately by the nonempty H2 handoff. -/
theorem nonemptyRibbonData_of_rf2_prefix_read
    (baseRow : ResetPortBaseRow)
    (rf2 : RF2SkewProductData baseRow)
    (prefixTable : PrefixPathTable baseRow)
    (read : RowWordReadTable baseRow) :
    Nonempty RibbonData :=
  nonemptyRibbonData_of_paperTableInput
    (paperTableInput_of_rf2_prefix_read baseRow rf2 prefixTable read)

/-- Final certificate assembly from the three independent H2 artifacts. -/
theorem lowD5M4RootFlatFamily_of_rf2_prefix_read
    (baseRow : ResetPortBaseRow)
    (rf2 : RF2SkewProductData baseRow)
    (prefixTable : PrefixPathTable baseRow)
    (read : RowWordReadTable baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  lowD5M4RootFlatFamily_of_paperTableInput
    (paperTableInput_of_rf2_prefix_read baseRow rf2 prefixTable read)

end D5M4RibbonRows
end V28Hard
end EvenV11
