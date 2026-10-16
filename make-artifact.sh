#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT="$ROOT/artifact"

BUILD=0
FORCE=0
for arg in "$@"; do
  case "$arg" in
    --build) BUILD=1 ;;
    --force) FORCE=1 ;;
    *) echo "usage: $0 [--force] [--build]" >&2; exit 2 ;;
  esac
done

if [ -e "$OUT" ]; then
  if [ "$FORCE" -eq 1 ]; then
    rm -rf "$OUT"
  else
    echo "error: $OUT already exists (use --force to overwrite)" >&2
    exit 1
  fi
fi

COMMON=(
  Common/Blame.v
  Common/CompCertExtensions.v
  Common/CoqMaps.v
  Common/Definitions.v
  Common/Either.v
  Common/Linking.v
  Common/Maps.v
  Common/Memory.v
  Common/SmallstepUB.v
  Common/Traces.v
  Common/Util.v
  Common/Values.v
  CompCert/Behaviors.v
  CompCert/Coqlib.v
  CompCert/Events.v
  CompCert/Smallstep.v
  Lib/Extra.v
  Lib/Monads.v
  Lib/Tactics.v
)

RSC_DC_MD=(
  RSC_DC_MD_Sigs.v
  RSC_DC_MD_Target.v
)

MP_BASE=(
  MicroPolicies/Utils.v
  MicroPolicies/Types.v
  MicroPolicies/WordExtra.v
  MicroPolicies/Int32.v
  MicroPolicies/Symbolic.v
  MicroPolicies/Exec.v
  MicroPolicies/LRC.v
  MicroPolicies/Instance.v
  MicroPolicies/Transitional.v
  MicroPolicies/Merged.v
)

RECOMP_BASE=(
  MicroPolicies/Recomposition/Definitions.v
  MicroPolicies/Recomposition/LabelScheme.v
  MicroPolicies/Recomposition/OffsetWord.v
  MicroPolicies/Recomposition/EncodeCode.v
  MicroPolicies/Recomposition/BufferLayout.v
  MicroPolicies/Recomposition/BufferShape.v
  MicroPolicies/Recomposition/PreservationLemmas.v
  MicroPolicies/Recomposition/StepSilentStrong.v
  MicroPolicies/Recomposition/StepSilentStrong2.v
  MicroPolicies/Recomposition/StepSilentWeak.v
  MicroPolicies/Recomposition/StepSilentWeak2.v
  MicroPolicies/Recomposition/StepEventCall.v
  MicroPolicies/Recomposition/StepEventReturn.v
  MicroPolicies/Recomposition/RecompositionInit.v
  MicroPolicies/Recomposition/PcColor.v
  MicroPolicies/Recomposition/RecBackward.v
  MicroPolicies/Recomposition/RecompositionTop.v
)

RECOMP_TAIL=(
  MicroPolicies/Recomposition/RSCDefs.v
  MicroPolicies/Recomposition/TraceWF.v
  MicroPolicies/Recomposition/TraceBracket.v
  MicroPolicies/Recomposition/TraceInit.v
  MicroPolicies/Recomposition/LinearizeMerged.v
  MicroPolicies/Recomposition/BackTranslation.v
)

FRONT_BASE=(
  Source/Language.v
  Source/GlobalEnv.v
  Source/CS.v
)

INTERMEDIATE=(
  Intermediate/Machine.v
  Intermediate/GlobalEnv.v
  Intermediate/CS.v
  I2MP/Tmp.v
  Extraction/Definitions.v
)

S2I_BASE=(
  S2I/Definitions.v
  S2I/CompMonad.v
  S2I/Compiler.v
)

RSC_DC_MD_MP=(
  RSC_DC_MD_MicroPolicies.v
  BackTranslationMeMP/Backtranslation_ME_MP.v
  BackTranslationMeMP/Backtranslation_ME_MP_Step.v
  BackTranslationMeMP/Backtranslation_ME_MP_Seg.v
  BackTranslationMeMP/Backtranslation_ME_MP_Alloc.v
  BackTranslationMeMP/Backtranslation_ME_MP_Layout.v
  BackTranslationMeMP/Backtranslation_ME_MP_Run.v
  BackTranslationMeMP/Backtranslation_ME_MP_Pos.v
  BackTranslationMeMP/Backtranslation_ME_MP_Trace.v
  BackTranslationMeMP/Backtranslation_ME_MP_Wf.v
  BackTranslationMeMP/Backtranslation_ME_MP_Sim.v
  BackTranslationMeMP/Backtranslation_ME_MP_Obs.v
  BackTranslationMeMP/Backtranslation_ME_MP_Pkg.v
  BackTranslationMeMP/Backtranslation_ME_MP_Inst.v
  "${MP_BASE[@]}"
  "${RECOMP_BASE[@]}"
  "${RECOMP_TAIL[@]}"
  MicroPolicies/Recomposition/RSC_ME_MP.v
  MicroPolicies/Recomposition/RSC_ME_MP_Faithful.v
  T2M/MPos.v
  T2M/MMemBase.v
  "${FRONT_BASE[@]}"
  Source/Definability.v
  "${S2I_BASE[@]}"
  "${INTERMEDIATE[@]}"
)

CHAIN=(
  ConcreteExample.v
  RSC_DC_MD_CompilationChainMP.v
  MicroPolicies/Recomposition/RSC_ME_MP.v
  MicroPolicies/Recomposition/RSC_ME_MP_Faithful.v
  "${FRONT_BASE[@]}"
  Source/Blame.v
  Source/Definability.v
  S2T/TSem.v
  S2T/TMem.v
  S2T/TInv.v
  S2T/TLabel.v
  S2T/TMacros.v
  S2T/TDrain.v
  S2T/TInject.v
  S2T/TStack.v
  S2T/TStackMatch.v
  S2T/TMatch.v
  S2T/TProlog.v
  S2T/TDiagram.v
  S2T/TLeaf.v
  S2T/TSim.v
  S2T/TStatic.v
  S2T/TStart.v
  S2T/TFull.v
  T2M/MDefs.v
  T2M/MFlip.v
  T2M/MHeap.v
  T2M/MMem.v
  T2M/MPos.v
  T2M/MMemBase.v
  T2M/MPosT.v
  T2M/MSig.v
  T2M/MBnz.v
  T2M/MCoh.v
  T2M/MDisc.v
  T2M/MDiscStepA.v
  T2M/MDiscStepA2.v
  T2M/MDiscStepB.v
  T2M/MDiscStepC.v
  T2M/MDiscStepD.v
  T2M/MInj.v
  T2M/MMatch.v
  T2M/MStep.v
  T2M/MSync.v
  T2M/MAlloc.v
  T2M/MInit.v
  T2M/MStar.v
  T2M/MWalk.v
  T2M/MDiscInit.v
  T2M/MStatic.v
  T2M/MStatic2.v
  T2M/MBwdSrc.v
  T2M/MInstance.v
  "${MP_BASE[@]}"
  MicroPolicies/RSC_MD_MP.v
  "${RECOMP_BASE[@]}"
  MicroPolicies/Recomposition/RSCSigs.v
  "${RECOMP_TAIL[@]}"
  "${S2I_BASE[@]}"
  S2I/LabelUniq.v
  S2I/SimInject.v
  S2I/SimCode.v
  S2I/Simulation.v
  "${INTERMEDIATE[@]}"
)

copy_files() {
  local dest="$1"; shift
  local f
  for f in "$@"; do
    if [ ! -f "$ROOT/$f" ]; then
      echo "error: missing source file $f" >&2
      exit 1
    fi
    mkdir -p "$dest/$(dirname "$f")"
    cp "$ROOT/$f" "$dest/$f"
  done
}

write_coqproject() {
  local dest="$1"; local with_common="$2"; shift 2
  {
    echo '-arg "-w -parsing"'
    if [ "$with_common" -eq 1 ]; then
      echo '-R ../common/Common RobustImp.Common'
      echo '-R ../common/CompCert RobustImp.CompCert'
      echo '-R ../common/Lib RobustImp.Lib'
    fi
    echo '-R . RobustImp'
    echo
    printf '%s\n' "$@"
  } > "$dest/_CoqProject"
}

write_submakefile() {
  cat > "$1/Makefile" <<'EOF'
all: Makefile.coq
	$(MAKE) -f Makefile.coq all

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d

.PHONY: all clean
EOF
}

make_project() {
  local name="$1"; local with_common="$2"; shift 2
  local dest="$OUT/$name"
  mkdir -p "$dest"
  copy_files "$dest" "$@"
  write_coqproject "$dest" "$with_common" "$@"
  write_submakefile "$dest"
}

strip_comments() {
  perl - "$@" <<'PERL'
use strict; use warnings;
local $/;
for my $f (@ARGV) {
  open my $h, '<', $f or die "$f: $!"; my $s = <$h>; close $h;
  my $out = ''; my $depth = 0; my $instr = 0; my $n = length $s;
  for (my $i = 0; $i < $n; $i++) {
    my $ch = substr($s, $i, 1);
    my $two = substr($s, $i, 2);
    if ($depth == 0) {
      if ($instr) {
        $out .= $ch;
        if ($ch eq '"') {
          if (substr($s, $i + 1, 1) eq '"') { $out .= '"'; $i++; } else { $instr = 0; }
        }
        next;
      }
      if ($ch eq '"') { $instr = 1; $out .= $ch; next; }
      if ($two eq '(*') { $depth = 1; $i++; next; }
      $out .= $ch;
    } else {
      if ($two eq '(*') { $depth++; $i++; next; }
      if ($two eq '*)') { $depth--; $i++; next; }
      if ($ch eq '"') {
        my $j = $i + 1;
        while ($j < $n) {
          if (substr($s, $j, 1) eq '"') {
            if (substr($s, $j + 1, 1) eq '"') { $j += 2; next; }
            last;
          }
          $j++;
        }
        $i = $j;
        next;
      }
    }
  }
  die "$f: unterminated comment\n" if $depth;
  $out =~ s/[ \t]+$//mg;
  $out =~ s/\n{3,}/\n\n/g;
  $out =~ s/\A\n+//;
  open my $o, '>', $f or die "$f: $!"; print $o $out; close $o;
}
PERL
}

mkdir -p "$OUT"
make_project common 0 "${COMMON[@]}"
make_project rsc_dc_md 1 "${RSC_DC_MD[@]}"
make_project rsc_dc_md_micropolicies 1 "${RSC_DC_MD_MP[@]}"
make_project compilation_chain 1 "${CHAIN[@]}"

find "$OUT" -name '*.v' -print0 | xargs -0 bash -c "$(declare -f strip_comments); strip_comments \"\$@\"" _

cp "$ROOT/README_rsc_dc_md.md" "$OUT/rsc_dc_md/README.md"
cp "$ROOT/README_rsc_dc_md_micropolicies.md" "$OUT/rsc_dc_md_micropolicies/README.md"
cp "$ROOT/README_compilation_chain.md" "$OUT/compilation_chain/README.md"

cat > "$OUT/Makefile" <<'EOF'
PROJECTS = rsc_dc_md rsc_dc_md_micropolicies compilation_chain

all: $(PROJECTS)

common:
	$(MAKE) -C common

$(PROJECTS): common
	$(MAKE) -C $@

clean:
	for d in common $(PROJECTS); do $(MAKE) -C $$d clean; done

.PHONY: all clean common $(PROJECTS)
EOF

echo "artifact written to $OUT"

if [ "$BUILD" -eq 1 ]; then
  make -C "$OUT" -j4
fi
