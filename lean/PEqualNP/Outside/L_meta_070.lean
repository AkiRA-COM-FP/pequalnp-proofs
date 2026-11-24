import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_070

open PEqualNP.CircuitLowerBounds

-- The circuit for the truth table whose entry at position a + 2 b + 4 c is the table bit
-- with that index.
def circ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Circuit :=
  bif b7 then
    bif b6 then
      bif b5 then
        bif b4 then
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, []⟩], 3⟩
                else
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩], 4⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [3, 4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.or, [1, 2]⟩], 3⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [3, 4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.or, [0, 2]⟩], 3⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [5, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩], 4⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [2, 4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [2, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [2, 3]⟩], 4⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 4]⟩], 5⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.or, [2, 3]⟩], 4⟩
                else
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [2, 4]⟩], 5⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [2, 4]⟩], 5⟩
                else
                  ⟨[], 2⟩
        else
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [3, 4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.or, [0, 1]⟩], 3⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [5, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [1, 3]⟩], 4⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩], 4⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [7, 8]⟩], 9⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [3, 5]⟩], 6⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [5, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩], 4⟩
      else
        bif b4 then
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [1, 4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [1, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 3]⟩], 4⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [1, 4]⟩], 5⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [5, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [3, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [3, 8]⟩], 9⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [5, 7]⟩], 8⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [2, 4]⟩], 5⟩
        else
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.or, [1, 3]⟩], 4⟩
                else
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [1, 4]⟩], 5⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [1, 4]⟩], 5⟩
                else
                  ⟨[], 1⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩], 4⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [5, 7]⟩], 8⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 4]⟩], 5⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [3, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [3, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩], 3⟩
    else
      bif b5 then
        bif b4 then
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [0, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [5, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 3]⟩], 4⟩
                else
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 4]⟩], 5⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [3, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [3, 8]⟩], 9⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [3, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [6, 7]⟩], 8⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [3, 4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [2, 4]⟩], 5⟩
        else
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.or, [0, 3]⟩], 4⟩
                else
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [0, 4]⟩], 5⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 4]⟩], 5⟩
                else
                  ⟨[], 0⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩], 4⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [5, 7]⟩], 8⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [3, 6]⟩], 7⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 4]⟩], 5⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [3, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩], 3⟩
      else
        bif b4 then
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [3, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [3, 8]⟩], 9⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [3, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [6, 7]⟩], 8⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [3, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [6, 7]⟩], 8⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [3, 6]⟩], 7⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [4, 8]⟩], 9⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [7, 9]⟩], 10⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [4, 8]⟩], 9⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [4, 8]⟩], 9⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [2, 6]⟩], 7⟩
        else
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [3, 4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [1, 4]⟩], 5⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [0, 4]⟩], 5⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [3, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩], 3⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [4, 8]⟩], 9⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [1, 6]⟩], 7⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [0, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [4, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩], 4⟩
  else
    bif b6 then
      bif b5 then
        bif b4 then
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [5, 7]⟩], 8⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.not, [7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.not, [7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.not, [9]⟩], 10⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩], 4⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [4, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [3, 5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [5, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [2, 4]⟩], 5⟩
        else
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.not, [7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.or, [6, 9]⟩], 10⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.or, [7, 9]⟩], 10⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [8, 9]⟩], 10⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.and, [5, 8]⟩], 9⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.not, [7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [5, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [4, 6]⟩], 7⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [5, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [4, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.or, [7, 9]⟩], 10⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
      else
        bif b4 then
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.not, [3]⟩], 4⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [4, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.not, [5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.not, [7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [6, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.not, [4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [0]⟩], 3⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩], 5⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [3, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [2, 3]⟩], 4⟩
        else
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.not, [5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [5, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [1, 4]⟩], 5⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [5, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [4, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.or, [7, 9]⟩], 10⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [3, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [1, 3]⟩], 4⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [5, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [4, 7]⟩], 8⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [6, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩], 5⟩
    else
      bif b5 then
        bif b4 then
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [3]⟩], 4⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [4, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.not, [7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.not, [5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [6, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.not, [4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩], 3⟩
                else
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [3, 4]⟩], 5⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [3, 5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [2, 3]⟩], 4⟩
        else
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.not, [5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [6, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [5, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [0, 4]⟩], 5⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.or, [7, 9]⟩], 10⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [3, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [5, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [6, 7]⟩], 8⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [0, 3]⟩], 4⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [6, 7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [3, 4]⟩], 5⟩
      else
        bif b4 then
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [4, 6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.not, [6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.not, [7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [6, 7]⟩], 8⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.not, [6]⟩], 7⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [7, 8]⟩], 9⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.not, [4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.not, [4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [3]⟩], 4⟩
                else
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [2, 4]⟩], 5⟩
        else
          bif b3 then
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [2]⟩], 3⟩
                else
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [3, 4]⟩], 5⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.and, [1, 3]⟩], 4⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [5]⟩], 6⟩
                else
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.and, [0, 3]⟩], 4⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.not, [7]⟩], 8⟩
                else
                  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [3, 4]⟩], 5⟩
          else
            bif b2 then
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [4]⟩], 5⟩
                else
                  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [4, 6]⟩], 7⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [3]⟩], 4⟩
                else
                  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [1, 4]⟩], 5⟩
            else
              bif b1 then
                bif b0 then
                  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [3]⟩], 4⟩
                else
                  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [0, 4]⟩], 5⟩
              else
                bif b0 then
                  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [4]⟩], 5⟩
                else
                  ⟨[], 3⟩

-- The entry of the table b0 .. b7 at position a + 2 b + 4 c.
def sel (b0 b1 b2 b3 b4 b5 b6 b7 a b c : Bool) : Bool :=
  bif c then (bif b then (bif a then b7 else b6) else (bif a then b5 else b4))
  else (bif b then (bif a then b3 else b2) else (bif a then b1 else b0))

-- The operations allowed by FanInTwo.
def opOK : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | GateOp.mod _ => false
  | GateOp.maj => false

-- A gate allowed by FanInTwo.
def gateOK (g : Gate) : Bool := opOK g.op && decide (g.inputs.length ≤ 2)

theorem fan (C : Circuit) (h : C.gates.all gateOK = true) :
    PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  simp only [gateOK, Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨h2, h3⟩ := h1
  refine ⟨?_, h3⟩
  rcases g with ⟨op, ins⟩
  cases op <;> simp_all [opOK]

set_option maxRecDepth 100000 in
theorem shape : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (circ b0 b1 b2 b3 b4 b5 b6 b7).gates.all gateOK = true ∧ (circ b0 b1 b2 b3 b4 b5 b6 b7).size ≤ 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem key : ∀ b0 b1 b2 b3 b4 b5 b6 b7 a b c : Bool,
    (circ b0 b1 b2 b3 b4 b5 b6 b7).eval [a, b, c] = sel b0 b1 b2 b3 b4 b5 b6 b7 a b c := by
  decide +kernel

-- The input with bits a, b, c.
def pt (a b c : Bool) : Fin 3 → Bool := fun i => bif i.val == 0 then a else bif i.val == 1 then b else c

theorem pt_eta (x : Fin 3 → Bool) : pt (x 0) (x 1) (x 2) = x := by
  funext i
  fin_cases i <;> rfl

theorem sel_pt (g : (Fin 3 → Bool) → Bool) (a b c : Bool) :
    sel (g (pt false false false)) (g (pt true false false)) (g (pt false true false)) (g (pt true true false)) (g (pt false false true)) (g (pt true false true)) (g (pt false true true)) (g (pt true true true))
      a b c = g (pt a b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem ofFn3 (x : Fin 3 → Bool) : List.ofFn x = [x 0, x 1, x 2] := by
  simp [List.ofFn_succ]

theorem main : ∀ f : (Fin 3 → Bool) → Bool, PEqualNP.MetaComplexity.HasCircuitSize 3 f 8 := by
  intro f
  obtain ⟨h1, h2⟩ := shape (f (pt false false false)) (f (pt true false false)) (f (pt false true false)) (f (pt true true false)) (f (pt false false true)) (f (pt true false true)) (f (pt false true true)) (f (pt true true true))
  refine ⟨circ (f (pt false false false)) (f (pt true false false)) (f (pt false true false)) (f (pt true true false)) (f (pt false false true)) (f (pt true false true)) (f (pt false true true)) (f (pt true true true)), fan _ h1, h2, ?_⟩
  intro x
  rw [ofFn3, key, sel_pt f, pt_eta]

end PEqualNP.Outside.L_meta_070

theorem PEqualNP.Outside.L_meta_070 :
    ∀ f : (Fin 3 → Bool) → Bool, PEqualNP.MetaComplexity.HasCircuitSize 3 f 8 :=
  PEqualNP.Outside.L_meta_070.main
