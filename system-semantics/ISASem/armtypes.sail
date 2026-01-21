default Order dec

$include <concurrency_interface.sail>
$include "../armv9-instantiation-types/interfacetypes.sail"

type Level = range (-1, 4)

// The translation information provided with every memory access.
struct TranslationInfo = {
  regime : Regime,
  vmid : option(bits(16)),
  asid : option(bits(16)),
  va : bits(64),
  s1level : option(Level),
  s2info : option((bits(64), Level)),
  s1params: option(S1TTWParams),
  s2params: option(S2TTWParams),
  memattr: MemoryAttributes,
}

// The details of a data memory/synchonisation barrier
struct DxB = {
  domain : MBReqDomain,
  types : MBReqTypes,
  nXS : bool
}

// An Arm barrier
union Barrier = {
  Barrier_DSB : DxB,
  Barrier_DMB : DxB, // The nXS field is ignored from DMBs
  Barrier_ISB : unit,
  Barrier_SSBB : unit,
  Barrier_PSSBB : unit,
  Barrier_SB : unit,
}

struct TLBI = {
  rec: TLBIRecord,
  shareability : Shareability,
}

// This one is WIP and subject to change
// The main question is whether the FaultRecord is really needed, or can its
// information be transfered elsewhere.
struct Exn = {
  rec: ExceptionRecord,
  fault: option(FaultRecord)
}

// This the set of all Arm access types that are not covered by the generic
// interface access type.
union arm_acc_type = {
  // Streaming access from a LDNP/STNP or some CPY* instruction
  SAcc_STREAM : unit,
  // Vector access, the boolean means that is a streaming access
  SAcc_VEC : /* streaming access :*/ bool,
  // SVE access, the boolean means that is a streaming access
  SAcc_SVE : /* streaming access :*/ bool,
  // SME access, the boolean means that is a streaming access
  SAcc_SME : /* streaming access :*/ bool,
  // Unpriviledged access, the boolean means that is a streaming access
  SAcc_UNPRIV : /* streaming access :*/ bool,
  // Load and store multiple from Aarch32
  SAcc_A32LSMD : unit,
  // Atomic 64 bytes access from LD64B/ST64B and some weirder versions
  SAcc_ATOMICLS64 : unit,
  // Load-LOAcquire and Store-LORelease
  SAcc_LIMITEDORDERED : unit,
  // Non-faulting access (exact semantics unclear)
  SAcc_NONFAULT : unit,
  // Contiguous FF load, not first element
  SAcc_CNOTFIRST : unit,
  // MRS/MSR instruction used at EL1 and which is
  // converted to a memory access that uses the
  // EL2 translation regime
  SAcc_NV2REGISTER : unit,
  // Data cache maintenance
  SAcc_DC : unit,
  // Instruction cache maintenance
  SAcc_IC : unit,
  // DC ZVA instructions
  SAcc_DCZVA : unit,
  // Address translation with PAN permission checks
  SAcc_ATPAN : unit,
  // Address translation
  SAcc_AT : unit
}

function eq_Access_variety(x : Access_variety, y : Access_variety) -> bool = {
  match (x,y) {
    (AV_plain, AV_plain) => true,
    (AV_exclusive, AV_exclusive) => true,
    (AV_atomic_rmw, AV_atomic_rmv) => true,
    _ => false
  }
}

function eq_Access_strength(x : Access_strength, y : Access_strength) -> bool = {
  match (x,y) {
    (AS_normal, AS_normal) => true,
    (AS_rel_or_acq, AS_rel_or_acq) => true,
    (AS_acq_rcpc, AS_acq_rcpc) => true,
    _ => false
  }
}


overload operator == = { eq_Access_variety, eq_Access_strength }

function AccType_to_Access_kind(acc : AccType) -> Access_kind(arm_acc_type) = {
  match acc {
    AccType_NORMAL => AK_explicit(struct{variety = AV_plain, strength = AS_normal}),
    AccType_STREAM => AK_arch(SAcc_STREAM()),
    AccType_VEC => AK_arch(SAcc_VEC(false)),
    AccType_VECSTREAM => AK_arch(SAcc_VEC(true)),
    AccType_SVE => AK_arch(SAcc_SVE(false)),
    AccType_SVESTREAM => AK_arch(SAcc_SVE(true)),
    AccType_SME => AK_arch(SAcc_SME(false)),
    AccType_SMESTREAM => AK_arch(SAcc_SME(true)),
    AccType_UNPRIVSTREAM => AK_arch(SAcc_UNPRIV(true)),
    AccType_A32LSMD => AK_arch(SAcc_A32LSMD()),
    AccType_ATOMIC => AK_explicit(struct{variety = AV_exclusive, strength = AS_normal}),
    AccType_ATOMICRW => AK_explicit(struct{variety = AV_atomic_rmw, strength = AS_normal}),
    AccType_ORDERED => AK_explicit(struct {variety = AV_plain, strength = AS_rel_or_acq}),
    AccType_ORDEREDRW => undefined,
    AccType_ORDEREDATOMIC => AK_explicit(struct {variety = AV_exclusive, strength = AS_rel_or_acq}),
    AccType_ORDEREDATOMICRW => AK_explicit(struct {variety = AV_atomic_rmw, strength = AS_rel_or_acq}),
    AccType_ATOMICLS64 => AK_arch(SAcc_ATOMICLS64()),
    AccType_LIMITEDORDERED => AK_arch(SAcc_LIMITEDORDERED()),
    AccType_UNPRIV => AK_arch(SAcc_UNPRIV(false)),
    AccType_IFETCH => AK_ifetch(),
    AccType_TTW => AK_ttw(),
    AccType_NONFAULT => AK_arch(SAcc_NONFAULT()),
    AccType_CNOTFIRST => AK_arch(SAcc_CNOTFIRST()),
    AccType_NV2REGISTER => AK_arch(SAcc_NV2REGISTER()),
    AccType_DC => AK_arch(SAcc_DC()),
    AccType_IC => AK_arch(SAcc_IC()),
    AccType_DCZVA => AK_arch(SAcc_DCZVA()),
    AccType_ATPAN => AK_arch(SAcc_ATPAN()),
    AccType_AT => AK_arch(SAcc_AT()),
  }
}