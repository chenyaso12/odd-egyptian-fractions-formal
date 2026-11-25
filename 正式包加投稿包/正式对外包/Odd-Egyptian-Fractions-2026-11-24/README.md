# Short representations and counting with distinct odd unit fractions

24 November 2026

Read the [paper (PDF)](manuscript/odd_egyptian_fractions.pdf). The [TeX source](manuscript/odd_egyptian_fractions.tex) and [Markdown manuscript](manuscript/odd_egyptian_fractions.md) accompany the Lean formalization.

## What the Lean theorem proves

The [combined theorem](MathProblems/OddEgyptian/EnglishManuscript.lean) is `OddEgyptian.englishManuscript_of_threePrimeInput : OddEgyptian.ThreePrimeInput → OddEgyptian.EnglishManuscriptResults`. Its premise is a uniform lower bound for the number of ordered representations of a sufficiently large odd integer as the sum of three odd primes, allowing repetition. The formal proof starts from that premise. The manuscript gives its classical analytic reference in the appendix. The [weighted-to-unweighted conversion](MathProblems/OddEgyptian/PrimePowerBridge.lean) is part of the project.

| Manuscript claim | Fields of `EnglishManuscriptResults` | Source for the claim |
| --- | --- | --- |
| Theorem 1.1, uniform length and the maximum and mean at each odd denominator | `uniformLength`, `maximumAndMeanLength` | [LengthOptimality.lean](MathProblems/OddEgyptian/LengthOptimality.lean) |
| Theorem 1.2, least length when the largest denominator has prescribed prime divisors | `leastLengthWithPrescribedPrimes` | [PrimorialLength.lean](MathProblems/OddEgyptian/PrimorialLength.lean) |
| Theorem 1.3, common initial segment and total count at each sufficiently large odd length | `commonPrefix`, `totalCount` | [StructuredFamilies.lean](MathProblems/OddEgyptian/StructuredFamilies.lean), [CommonPrefix.lean](MathProblems/OddEgyptian/CommonPrefix.lean), [Definitions.lean](MathProblems/OddEgyptian/Definitions.lean) |
| Corollary 1.4, many distinct maxima and many representations at each of them | `multiplicityAtMaximum` | [StructuredFamilies.lean](MathProblems/OddEgyptian/StructuredFamilies.lean), [MultiplicityGrowth.lean](MathProblems/OddEgyptian/MultiplicityGrowth.lean) |

The [input definition](MathProblems/OddEgyptian/DigitInputs.lean) and the [audit program](MathProblems/OddEgyptian/Audit.lean) are included. The [recorded build and audit](verification/build-and-audit.txt) covers 365 declarations. The [recorded kernel replay](verification/kernel-replay.txt) lists 53 research modules, their exit codes and source hashes. The build used the mathlib revision pinned in [lake-manifest.json](lake-manifest.json).

## Build the PDF

This edition was typeset with Tectonic 0.17.0+20260731 (XeTeX backend). To rebuild it, run

```sh
cd manuscript
tectonic --untrusted --reruns 2 odd_egyptian_fractions.tex
```

With a XeLaTeX installation, run `xelatex odd_egyptian_fractions.tex` twice in the `manuscript` directory.

## Reproduce the Lean checks

Extract the archive and run these commands in the directory containing `lean-toolchain`. With Elan and Git available, Lake can fetch the pinned dependencies. The cache command downloads mathlib's compiled artifacts.

```text
lake env lean --version
lake exe cache get
lake build
lake env lean MathProblems/OddEgyptian/Audit.lean
```

The archived run used Lean 4.36.0. Look for `Axiom audit passed for 365 declarations.` and the explicit premise in the printed type of the combined theorem. The three allowed Lean axioms are `propext`, `Classical.choice` and `Quot.sound`.

To replay each research module after the build, run this loop in a POSIX shell. The audit file itself is checked by the preceding Lean command.

```sh
for f in MathProblems/OddEgyptian/*.lean; do
  name=$(basename "$f" .lean)
  [ "$name" = Audit ] && continue
  lake env leanchecker --verbose "MathProblems.OddEgyptian.$name" || exit 1
done
```

Alternatively, in PowerShell run

```powershell
Get-ChildItem MathProblems/OddEgyptian/*.lean |
  Where-Object BaseName -ne 'Audit' |
  ForEach-Object {
    lake env leanchecker --verbose "MathProblems.OddEgyptian.$($_.BaseName)"
    if ($LASTEXITCODE -ne 0) { throw "Replay failed for $($_.BaseName)" }
  }
```

[SHA256SUMS](SHA256SUMS) covers every other file in this archive. With GNU Coreutils, run `sha256sum -c SHA256SUMS` from this directory.
