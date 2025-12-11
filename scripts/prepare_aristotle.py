#!/usr/bin/env python3
"""
Prepare sections for Aristotle by inlining Common module dependencies.

Creates self-contained *_aristotle.lean files without Common imports.
"""

import argparse
from pathlib import Path
import re


COMMON_BASIC_INLINE = """/-
Common definitions inlined for Aristotle processing
-/

-- Currency represented in cents (to avoid floating point issues)
def Currency := Int
  deriving Repr, DecidableEq

namespace Currency

def make (dollars : Int) (cents : Nat) : Currency :=
  dollars * 100 + (cents : Int)

def zero : Currency := (0 : Int)

def toDollars (c : Currency) : Int :=
  let ci : Int := c
  ci / 100

instance : OfNat Currency n := ⟨(n : Int)⟩

instance : LE Currency where
  le a b := @LE.le Int _ a b

instance : LT Currency where
  lt a b := @LT.lt Int _ a b

-- Arithmetic instances for Currency (delegates to Int since Currency := Int)
instance : HAdd Currency Currency Currency where
  hAdd a b := Int.add a b

instance : HAdd Currency Int Currency where
  hAdd a b := Int.add a b

instance : HAdd Int Currency Currency where
  hAdd a b := Int.add a b

instance : HSub Currency Currency Currency where
  hSub a b := Int.sub a b

instance : HSub Currency Int Currency where
  hSub a b := Int.sub a b

instance : HSub Int Currency Currency where
  hSub a b := Int.sub a b

instance : HMul Currency Currency Currency where
  hMul a b := Int.mul a b

instance : HMul Currency Int Currency where
  hMul a b := Int.mul a b

instance : HMul Int Currency Currency where
  hMul a b := Int.mul a b

instance : HDiv Currency Int Currency where
  hDiv a b := Int.tdiv a b

instance : HDiv Currency Currency Currency where
  hDiv a b := Int.tdiv a b

instance : Max Currency where
  max a b := let ai : Int := a; let bi : Int := b; if ai ≤ bi then bi else ai

instance : Min Currency where
  min a b := let ai : Int := a; let bi : Int := b; if ai ≤ bi then ai else bi

instance : Neg Currency where
  neg a := Int.neg a

end Currency

-- Tax Year
structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913

namespace TaxYear

def current : TaxYear := ⟨2024, by decide⟩

instance : DecidableEq TaxYear := fun a b =>
  match a, b with
  | ⟨y1, _⟩, ⟨y2, _⟩ =>
    if h : y1 = y2 then
      isTrue (by cases h; rfl)
    else
      isFalse (by intro eq; cases eq; exact h rfl)

end TaxYear

-- Filing Status
inductive FilingStatus
  | Single
  | MarriedFilingJointly
  | MarriedFilingSeparately
  | HeadOfHousehold
  | QualifyingWidower
  deriving Repr, DecidableEq, Inhabited

structure Taxpayer where
  id : String
  filingStatus : FilingStatus
  taxYear : TaxYear

instance : Repr Taxpayer where
  reprPrec t _ := s!"Taxpayer(id: {t.id}, status: {repr t.filingStatus}, year: {t.taxYear.year})"
"""


def prepare_for_aristotle(section_num: str) -> bool:
    """Prepare a section file for Aristotle by inlining Common imports."""

    src_file = Path(f'src/TaxCode/Section{section_num}.lean')
    aristotle_file = Path(f'src/TaxCode/Section{section_num}_aristotle.lean')

    if not src_file.exists():
        print(f"Error: {src_file} not found")
        return False

    # Read original file
    content = src_file.read_text()

    # Replace Common.Basic import with inlined definitions
    if 'import Common.Basic' in content:
        content = re.sub(
            r'import Common\.Basic\n',
            COMMON_BASIC_INLINE + '\n',
            content
        )

    # Write Aristotle version
    aristotle_file.write_text(content)
    print(f"✓ Created {aristotle_file}")

    return True


def main():
    parser = argparse.ArgumentParser(description='Prepare sections for Aristotle')
    parser.add_argument('sections', type=str, help='Comma-separated section numbers')
    args = parser.parse_args()

    section_nums = [s.strip() for s in args.sections.split(',')]

    success_count = 0
    for section_num in section_nums:
        if prepare_for_aristotle(section_num):
            success_count += 1

    print(f"\n✓ Prepared {success_count}/{len(section_nums)} sections for Aristotle")

    return 0 if success_count == len(section_nums) else 1


if __name__ == '__main__':
    import sys
    sys.exit(main())
