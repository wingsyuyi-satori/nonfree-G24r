import TwentyFour.Core
import TwentyFour.FiniteCover

/-! Exact rational matrix certificates and reduced syllable certificates for all
23 numerical exceptions. These are finite computations checked by the kernel. -/
namespace TwentyFour
namespace FiniteWords
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def word_7 : List Syllable := syllables true [1, -1, 1, -1, 1, -1, 1, -5, -1, 1, -1, 21, -1, 1, -1]

theorem matrix_7 : matrixWord (24 / 7) word_7 =
    !![(1 / 2401 : ℚ), 0; (-410055 / 343 : ℚ), 2401] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_7, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_7 : ReducedSyllables (relationSyllables word_7) := by
  unfold ReducedSyllables
  decide

theorem nonempty_7 : relationSyllables word_7 ≠ [] := by decide

theorem length_7 : (relationSyllables word_7).length ≤ 64 := by decide

theorem evaluated_7 : eval (24 / 7) (word (relationSyllables word_7)) = 1 := by
  apply triangular_relation_eval (24 / 7) word_7
  rw [matrix_7]
  rfl

theorem nontrivial_7 : word (relationSyllables word_7) ≠ 1 :=
  word_ne_one reduced_7 nonempty_7

theorem relation_7 : HasRelation (24 / 7) := by
  apply triangular_hasRelation (24 / 7) word_7 reduced_7
  rw [matrix_7]
  rfl

def word_8 : List Syllable := syllables true [1, -1, 1, -1, 1]

theorem matrix_8 : matrixWord (24 / 8) word_8 =
    !![1, 0; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_8, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_8 : ReducedSyllables (relationSyllables word_8) := by
  unfold ReducedSyllables
  decide

theorem nonempty_8 : relationSyllables word_8 ≠ [] := by decide

theorem length_8 : (relationSyllables word_8).length ≤ 64 := by decide

theorem evaluated_8 : eval (24 / 8) (word (relationSyllables word_8)) = 1 := by
  apply triangular_relation_eval (24 / 8) word_8
  rw [matrix_8]
  rfl

theorem nontrivial_8 : word (relationSyllables word_8) ≠ 1 :=
  word_ne_one reduced_8 nonempty_8

theorem relation_8 : HasRelation (24 / 8) := by
  apply triangular_hasRelation (24 / 8) word_8 reduced_8
  rw [matrix_8]
  rfl

def word_9 : List Syllable := syllables true [1, -1, 1, -1, 6]

theorem matrix_9 : matrixWord (24 / 9) word_9 =
    !![(1 / 9 : ℚ), 0; (2 / 3 : ℚ), 9] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_9, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_9 : ReducedSyllables (relationSyllables word_9) := by
  unfold ReducedSyllables
  decide

theorem nonempty_9 : relationSyllables word_9 ≠ [] := by decide

theorem length_9 : (relationSyllables word_9).length ≤ 64 := by decide

theorem evaluated_9 : eval (24 / 9) (word (relationSyllables word_9)) = 1 := by
  apply triangular_relation_eval (24 / 9) word_9
  rw [matrix_9]
  rfl

theorem nontrivial_9 : word (relationSyllables word_9) ≠ 1 :=
  word_ne_one reduced_9 nonempty_9

theorem relation_9 : HasRelation (24 / 9) := by
  apply triangular_hasRelation (24 / 9) word_9 reduced_9
  rw [matrix_9]
  rfl

def word_10 : List Syllable := syllables true [1, -1, 1, -1, -1, 5, -1]

theorem matrix_10 : matrixWord (24 / 10) word_10 =
    !![(1 / 25 : ℚ), 0; (-57 / 5 : ℚ), 25] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_10, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_10 : ReducedSyllables (relationSyllables word_10) := by
  unfold ReducedSyllables
  decide

theorem nonempty_10 : relationSyllables word_10 ≠ [] := by decide

theorem length_10 : (relationSyllables word_10).length ≤ 64 := by decide

theorem evaluated_10 : eval (24 / 10) (word (relationSyllables word_10)) = 1 := by
  apply triangular_relation_eval (24 / 10) word_10
  rw [matrix_10]
  rfl

theorem nontrivial_10 : word (relationSyllables word_10) ≠ 1 :=
  word_ne_one reduced_10 nonempty_10

theorem relation_10 : HasRelation (24 / 10) := by
  apply triangular_hasRelation (24 / 10) word_10 reduced_10
  rw [matrix_10]
  rfl

def word_11 : List Syllable := syllables true [1, -1, 1, -3, 22]

theorem matrix_11 : matrixWord (24 / 11) word_11 =
    !![(1 / 121 : ℚ), 0; (28 / 11 : ℚ), 121] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_11, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_11 : ReducedSyllables (relationSyllables word_11) := by
  unfold ReducedSyllables
  decide

theorem nonempty_11 : relationSyllables word_11 ≠ [] := by decide

theorem length_11 : (relationSyllables word_11).length ≤ 64 := by decide

theorem evaluated_11 : eval (24 / 11) (word (relationSyllables word_11)) = 1 := by
  apply triangular_relation_eval (24 / 11) word_11
  rw [matrix_11]
  rfl

theorem nontrivial_11 : word (relationSyllables word_11) ≠ 1 :=
  word_ne_one reduced_11 nonempty_11

theorem relation_11 : HasRelation (24 / 11) := by
  apply triangular_hasRelation (24 / 11) word_11 reduced_11
  rw [matrix_11]
  rfl

def word_12 : List Syllable := syllables true [1, -1, 1]

theorem matrix_12 : matrixWord (24 / 12) word_12 =
    !![-1, 0; -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_12, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_12 : ReducedSyllables (relationSyllables word_12) := by
  unfold ReducedSyllables
  decide

theorem nonempty_12 : relationSyllables word_12 ≠ [] := by decide

theorem length_12 : (relationSyllables word_12).length ≤ 64 := by decide

theorem evaluated_12 : eval (24 / 12) (word (relationSyllables word_12)) = 1 := by
  apply triangular_relation_eval (24 / 12) word_12
  rw [matrix_12]
  rfl

theorem nontrivial_12 : word (relationSyllables word_12) ≠ 1 :=
  word_ne_one reduced_12 nonempty_12

theorem relation_12 : HasRelation (24 / 12) := by
  apply triangular_hasRelation (24 / 12) word_12 reduced_12
  rw [matrix_12]
  rfl

def word_13 : List Syllable := syllables true [1, -1, 1, 3, -26]

theorem matrix_13 : matrixWord (24 / 13) word_13 =
    !![(1 / 169 : ℚ), 0; (-46 / 13 : ℚ), 169] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_13, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_13 : ReducedSyllables (relationSyllables word_13) := by
  unfold ReducedSyllables
  decide

theorem nonempty_13 : relationSyllables word_13 ≠ [] := by decide

theorem length_13 : (relationSyllables word_13).length ≤ 64 := by decide

theorem evaluated_13 : eval (24 / 13) (word (relationSyllables word_13)) = 1 := by
  apply triangular_relation_eval (24 / 13) word_13
  rw [matrix_13]
  rfl

theorem nontrivial_13 : word (relationSyllables word_13) ≠ 1 :=
  word_ne_one reduced_13 nonempty_13

theorem relation_13 : HasRelation (24 / 13) := by
  apply triangular_hasRelation (24 / 13) word_13 reduced_13
  rw [matrix_13]
  rfl

def word_14 : List Syllable := syllables true [1, -1, 1, 1, 1, 2, 4, 3, -7]

theorem matrix_14 : matrixWord (24 / 14) word_14 =
    !![(1 / 2401 : ℚ), 0; (-70501 / 343 : ℚ), 2401] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_14, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_14 : ReducedSyllables (relationSyllables word_14) := by
  unfold ReducedSyllables
  decide

theorem nonempty_14 : relationSyllables word_14 ≠ [] := by decide

theorem length_14 : (relationSyllables word_14).length ≤ 64 := by decide

theorem evaluated_14 : eval (24 / 14) (word (relationSyllables word_14)) = 1 := by
  apply triangular_relation_eval (24 / 14) word_14
  rw [matrix_14]
  rfl

theorem nontrivial_14 : word (relationSyllables word_14) ≠ 1 :=
  word_ne_one reduced_14 nonempty_14

theorem relation_14 : HasRelation (24 / 14) := by
  apply triangular_hasRelation (24 / 14) word_14 reduced_14
  rw [matrix_14]
  rfl

def word_17 : List Syllable := syllables true [15, -1, 1, -3, 3, -19, 4, 8, -119]

theorem matrix_17 : matrixWord (24 / 17) word_17 =
    !![(1 / 83521 : ℚ), 0; (-2444271 / 4913 : ℚ), 83521] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_17, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_17 : ReducedSyllables (relationSyllables word_17) := by
  unfold ReducedSyllables
  decide

theorem nonempty_17 : relationSyllables word_17 ≠ [] := by decide

theorem length_17 : (relationSyllables word_17).length ≤ 64 := by decide

theorem evaluated_17 : eval (24 / 17) (word (relationSyllables word_17)) = 1 := by
  apply triangular_relation_eval (24 / 17) word_17
  rw [matrix_17]
  rfl

theorem nontrivial_17 : word (relationSyllables word_17) ≠ 1 :=
  word_ne_one reduced_17 nonempty_17

theorem relation_17 : HasRelation (24 / 17) := by
  apply triangular_hasRelation (24 / 17) word_17 reduced_17
  rw [matrix_17]
  rfl

def word_24 : List Syllable := syllables true [2, -1, 2]

theorem matrix_24 : matrixWord (24 / 24) word_24 =
    !![-1, 0; -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_24, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_24 : ReducedSyllables (relationSyllables word_24) := by
  unfold ReducedSyllables
  decide

theorem nonempty_24 : relationSyllables word_24 ≠ [] := by decide

theorem length_24 : (relationSyllables word_24).length ≤ 64 := by decide

theorem evaluated_24 : eval (24 / 24) (word (relationSyllables word_24)) = 1 := by
  apply triangular_relation_eval (24 / 24) word_24
  rw [matrix_24]
  rfl

theorem nontrivial_24 : word (relationSyllables word_24) ≠ 1 :=
  word_ne_one reduced_24 nonempty_24

theorem relation_24 : HasRelation (24 / 24) := by
  apply triangular_hasRelation (24 / 24) word_24 reduced_24
  rw [matrix_24]
  rfl

def word_31 : List Syllable := syllables true [1, -1, -4, -3, -93]

theorem matrix_31 : matrixWord (24 / 31) word_31 =
    !![(1 / 961 : ℚ), 0; (-412 / 31 : ℚ), 961] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_31, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_31 : ReducedSyllables (relationSyllables word_31) := by
  unfold ReducedSyllables
  decide

theorem nonempty_31 : relationSyllables word_31 ≠ [] := by decide

theorem length_31 : (relationSyllables word_31).length ≤ 64 := by decide

theorem evaluated_31 : eval (24 / 31) (word (relationSyllables word_31)) = 1 := by
  apply triangular_relation_eval (24 / 31) word_31
  rw [matrix_31]
  rfl

theorem nontrivial_31 : word (relationSyllables word_31) ≠ 1 :=
  word_ne_one reduced_31 nonempty_31

theorem relation_31 : HasRelation (24 / 31) := by
  apply triangular_hasRelation (24 / 31) word_31 reduced_31
  rw [matrix_31]
  rfl

def word_35 : List Syllable := syllables true [2, -1, 5, 4, -7]

theorem matrix_35 : matrixWord (24 / 35) word_35 =
    !![(1 / 49 : ℚ), 0; (-75 / 7 : ℚ), 49] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_35, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_35 : ReducedSyllables (relationSyllables word_35) := by
  unfold ReducedSyllables
  decide

theorem nonempty_35 : relationSyllables word_35 ≠ [] := by decide

theorem length_35 : (relationSyllables word_35).length ≤ 64 := by decide

theorem evaluated_35 : eval (24 / 35) (word (relationSyllables word_35)) = 1 := by
  apply triangular_relation_eval (24 / 35) word_35
  rw [matrix_35]
  rfl

theorem nontrivial_35 : word (relationSyllables word_35) ≠ 1 :=
  word_ne_one reduced_35 nonempty_35

theorem relation_35 : HasRelation (24 / 35) := by
  apply triangular_hasRelation (24 / 35) word_35 reduced_35
  rw [matrix_35]
  rfl

def word_37 : List Syllable := syllables true [3, -1, 3, 9, -222]

theorem matrix_37 : matrixWord (24 / 37) word_37 =
    !![(1 / 1369 : ℚ), 0; (-352 / 37 : ℚ), 1369] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_37, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_37 : ReducedSyllables (relationSyllables word_37) := by
  unfold ReducedSyllables
  decide

theorem nonempty_37 : relationSyllables word_37 ≠ [] := by decide

theorem length_37 : (relationSyllables word_37).length ≤ 64 := by decide

theorem evaluated_37 : eval (24 / 37) (word (relationSyllables word_37)) = 1 := by
  apply triangular_relation_eval (24 / 37) word_37
  rw [matrix_37]
  rfl

theorem nontrivial_37 : word (relationSyllables word_37) ≠ 1 :=
  word_ne_one reduced_37 nonempty_37

theorem relation_37 : HasRelation (24 / 37) := by
  apply triangular_hasRelation (24 / 37) word_37 reduced_37
  rw [matrix_37]
  rfl

def word_59 : List Syllable := syllables true [2, -1, -11, 9, 177]

theorem matrix_59 : matrixWord (24 / 59) word_59 =
    !![(1 / 3481 : ℚ), 0; (2848 / 59 : ℚ), 3481] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_59, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_59 : ReducedSyllables (relationSyllables word_59) := by
  unfold ReducedSyllables
  decide

theorem nonempty_59 : relationSyllables word_59 ≠ [] := by decide

theorem length_59 : (relationSyllables word_59).length ≤ 64 := by decide

theorem evaluated_59 : eval (24 / 59) (word (relationSyllables word_59)) = 1 := by
  apply triangular_relation_eval (24 / 59) word_59
  rw [matrix_59]
  rfl

theorem nontrivial_59 : word (relationSyllables word_59) ≠ 1 :=
  word_ne_one reduced_59 nonempty_59

theorem relation_59 : HasRelation (24 / 59) := by
  apply triangular_hasRelation (24 / 59) word_59 reduced_59
  rw [matrix_59]
  rfl

def word_61 : List Syllable := syllables true [4, -1, 7, -89, 61]

theorem matrix_61 : matrixWord (24 / 61) word_61 =
    !![(1 / 3721 : ℚ), 0; (9462 / 61 : ℚ), 3721] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_61, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_61 : ReducedSyllables (relationSyllables word_61) := by
  unfold ReducedSyllables
  decide

theorem nonempty_61 : relationSyllables word_61 ≠ [] := by decide

theorem length_61 : (relationSyllables word_61).length ≤ 64 := by decide

theorem evaluated_61 : eval (24 / 61) (word (relationSyllables word_61)) = 1 := by
  apply triangular_relation_eval (24 / 61) word_61
  rw [matrix_61]
  rfl

theorem nontrivial_61 : word (relationSyllables word_61) ≠ 1 :=
  word_ne_one reduced_61 nonempty_61

theorem relation_61 : HasRelation (24 / 61) := by
  apply triangular_hasRelation (24 / 61) word_61 reduced_61
  rw [matrix_61]
  rfl

def word_83 : List Syllable := syllables true [2, -2, 13, -15, 249]

theorem matrix_83 : matrixWord (24 / 83) word_83 =
    !![(1 / 6889 : ℚ), 0; (7949 / 83 : ℚ), 6889] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_83, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_83 : ReducedSyllables (relationSyllables word_83) := by
  unfold ReducedSyllables
  decide

theorem nonempty_83 : relationSyllables word_83 ≠ [] := by decide

theorem length_83 : (relationSyllables word_83).length ≤ 64 := by decide

theorem evaluated_83 : eval (24 / 83) (word (relationSyllables word_83)) = 1 := by
  apply triangular_relation_eval (24 / 83) word_83
  rw [matrix_83]
  rfl

theorem nontrivial_83 : word (relationSyllables word_83) ≠ 1 :=
  word_ne_one reduced_83 nonempty_83

theorem relation_83 : HasRelation (24 / 83) := by
  apply triangular_hasRelation (24 / 83) word_83 reduced_83
  rw [matrix_83]
  rfl

def word_85 : List Syllable := syllables true [2, -2, 15, 8, -17]

theorem matrix_85 : matrixWord (24 / 85) word_85 =
    !![(1 / 289 : ℚ), 0; (-1050 / 17 : ℚ), 289] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_85, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_85 : ReducedSyllables (relationSyllables word_85) := by
  unfold ReducedSyllables
  decide

theorem nonempty_85 : relationSyllables word_85 ≠ [] := by decide

theorem length_85 : (relationSyllables word_85).length ≤ 64 := by decide

theorem evaluated_85 : eval (24 / 85) (word (relationSyllables word_85)) = 1 := by
  apply triangular_relation_eval (24 / 85) word_85
  rw [matrix_85]
  rfl

theorem nontrivial_85 : word (relationSyllables word_85) ≠ 1 :=
  word_ne_one reduced_85 nonempty_85

theorem relation_85 : HasRelation (24 / 85) := by
  apply triangular_hasRelation (24 / 85) word_85 reduced_85
  rw [matrix_85]
  rfl

def word_107 : List Syllable := syllables true [4, -1, -39, 49, 107]

theorem matrix_107 : matrixWord (24 / 107) word_107 =
    !![(1 / 11449 : ℚ), 0; (51000 / 107 : ℚ), 11449] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_107, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_107 : ReducedSyllables (relationSyllables word_107) := by
  unfold ReducedSyllables
  decide

theorem nonempty_107 : relationSyllables word_107 ≠ [] := by decide

theorem length_107 : (relationSyllables word_107).length ≤ 64 := by decide

theorem evaluated_107 : eval (24 / 107) (word (relationSyllables word_107)) = 1 := by
  apply triangular_relation_eval (24 / 107) word_107
  rw [matrix_107]
  rfl

theorem nontrivial_107 : word (relationSyllables word_107) ≠ 1 :=
  word_ne_one reduced_107 nonempty_107

theorem relation_107 : HasRelation (24 / 107) := by
  apply triangular_hasRelation (24 / 107) word_107 reduced_107
  rw [matrix_107]
  rfl

def word_109 : List Syllable := syllables true [1, -5, 10, -50, 109]

theorem matrix_109 : matrixWord (24 / 109) word_109 =
    !![(1 / 11881 : ℚ), 0; (54005 / 109 : ℚ), 11881] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_109, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_109 : ReducedSyllables (relationSyllables word_109) := by
  unfold ReducedSyllables
  decide

theorem nonempty_109 : relationSyllables word_109 ≠ [] := by decide

theorem length_109 : (relationSyllables word_109).length ≤ 64 := by decide

theorem evaluated_109 : eval (24 / 109) (word (relationSyllables word_109)) = 1 := by
  apply triangular_relation_eval (24 / 109) word_109
  rw [matrix_109]
  rfl

theorem nontrivial_109 : word (relationSyllables word_109) ≠ 1 :=
  word_ne_one reduced_109 nonempty_109

theorem relation_109 : HasRelation (24 / 109) := by
  apply triangular_hasRelation (24 / 109) word_109 reduced_109
  rw [matrix_109]
  rfl

def word_613 : List Syllable := syllables true [25, -1, -1179, 166, 1226]

theorem matrix_613 : matrixWord (24 / 613) word_613 =
    !![(1 / 375769 : ℚ), 0; (4798281 / 613 : ℚ), 375769] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_613, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_613 : ReducedSyllables (relationSyllables word_613) := by
  unfold ReducedSyllables
  decide

theorem nonempty_613 : relationSyllables word_613 ≠ [] := by decide

theorem length_613 : (relationSyllables word_613).length ≤ 64 := by decide

theorem evaluated_613 : eval (24 / 613) (word (relationSyllables word_613)) = 1 := by
  apply triangular_relation_eval (24 / 613) word_613
  rw [matrix_613]
  rfl

theorem nontrivial_613 : word (relationSyllables word_613) ≠ 1 :=
  word_ne_one reduced_613 nonempty_613

theorem relation_613 : HasRelation (24 / 613) := by
  apply triangular_hasRelation (24 / 613) word_613 reduced_613
  rw [matrix_613]
  rfl

def word_877 : List Syllable := syllables true [2, -18, -135, 475, 877]

theorem matrix_877 : matrixWord (24 / 877) word_877 =
    !![(1 / 769129 : ℚ), 0; (28102789 / 877 : ℚ), 769129] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_877, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_877 : ReducedSyllables (relationSyllables word_877) := by
  unfold ReducedSyllables
  decide

theorem nonempty_877 : relationSyllables word_877 ≠ [] := by decide

theorem length_877 : (relationSyllables word_877).length ≤ 64 := by decide

theorem evaluated_877 : eval (24 / 877) (word (relationSyllables word_877)) = 1 := by
  apply triangular_relation_eval (24 / 877) word_877
  rw [matrix_877]
  rfl

theorem nontrivial_877 : word (relationSyllables word_877) ≠ 1 :=
  word_ne_one reduced_877 nonempty_877

theorem relation_877 : HasRelation (24 / 877) := by
  apply triangular_hasRelation (24 / 877) word_877 reduced_877
  rw [matrix_877]
  rfl

def word_1139 : List Syllable := syllables true [8, -6, 701, -617, 1139]

theorem matrix_1139 : matrixWord (24 / 1139) word_1139 =
    !![(1 / 1297321 : ℚ), 0; (61572851 / 1139 : ℚ), 1297321] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_1139, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_1139 : ReducedSyllables (relationSyllables word_1139) := by
  unfold ReducedSyllables
  decide

theorem nonempty_1139 : relationSyllables word_1139 ≠ [] := by decide

theorem length_1139 : (relationSyllables word_1139).length ≤ 64 := by decide

theorem evaluated_1139 : eval (24 / 1139) (word (relationSyllables word_1139)) = 1 := by
  apply triangular_relation_eval (24 / 1139) word_1139
  rw [matrix_1139]
  rfl

theorem nontrivial_1139 : word (relationSyllables word_1139) ≠ 1 :=
  word_ne_one reduced_1139 nonempty_1139

theorem relation_1139 : HasRelation (24 / 1139) := by
  apply triangular_hasRelation (24 / 1139) word_1139 reduced_1139
  rw [matrix_1139]
  rfl

def word_2267 : List Syllable := syllables true [1, -94, -206, -1039, -2267]

theorem matrix_2267 : matrixWord (24 / 2267) word_2267 =
    !![(1 / 5139289 : ℚ), 0; (-485429215 / 2267 : ℚ), 5139289] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixWord, word_2267, syllables, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem reduced_2267 : ReducedSyllables (relationSyllables word_2267) := by
  unfold ReducedSyllables
  decide

theorem nonempty_2267 : relationSyllables word_2267 ≠ [] := by decide

theorem length_2267 : (relationSyllables word_2267).length ≤ 64 := by decide

theorem evaluated_2267 : eval (24 / 2267) (word (relationSyllables word_2267)) = 1 := by
  apply triangular_relation_eval (24 / 2267) word_2267
  rw [matrix_2267]
  rfl

theorem nontrivial_2267 : word (relationSyllables word_2267) ≠ 1 :=
  word_ne_one reduced_2267 nonempty_2267

theorem relation_2267 : HasRelation (24 / 2267) := by
  apply triangular_hasRelation (24 / 2267) word_2267 reduced_2267
  rw [matrix_2267]
  rfl

theorem exception_hasRelation (r : Nat) (hr : r ∈ FiniteCover.exceptionValues) :
    HasRelation (24 / (r : ℚ)) := by
  simp only [FiniteCover.exceptionValues, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst r
    exact relation_7
  · subst r
    exact relation_8
  · subst r
    exact relation_9
  · subst r
    exact relation_10
  · subst r
    exact relation_11
  · subst r
    exact relation_12
  · subst r
    exact relation_13
  · subst r
    exact relation_14
  · subst r
    exact relation_17
  · subst r
    exact relation_24
  · subst r
    exact relation_31
  · subst r
    exact relation_35
  · subst r
    exact relation_37
  · subst r
    exact relation_59
  · subst r
    exact relation_61
  · subst r
    exact relation_83
  · subst r
    exact relation_85
  · subst r
    exact relation_107
  · subst r
    exact relation_109
  · subst r
    exact relation_613
  · subst r
    exact relation_877
  · subst r
    exact relation_1139
  · subst r
    exact relation_2267

theorem exception_certificate (r : Nat) (hr : r ∈ FiniteCover.exceptionValues) :
    ∃ l : List Syllable, ReducedSyllables l ∧ l ≠ [] ∧ l.length ≤ 64 ∧
      word l ≠ 1 ∧ eval (24 / (r : ℚ)) (word l) = 1 := by
  simp only [FiniteCover.exceptionValues, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst r
    exact ⟨relationSyllables word_7, reduced_7, nonempty_7, length_7, nontrivial_7, evaluated_7⟩
  · subst r
    exact ⟨relationSyllables word_8, reduced_8, nonempty_8, length_8, nontrivial_8, evaluated_8⟩
  · subst r
    exact ⟨relationSyllables word_9, reduced_9, nonempty_9, length_9, nontrivial_9, evaluated_9⟩
  · subst r
    exact ⟨relationSyllables word_10, reduced_10, nonempty_10, length_10, nontrivial_10, evaluated_10⟩
  · subst r
    exact ⟨relationSyllables word_11, reduced_11, nonempty_11, length_11, nontrivial_11, evaluated_11⟩
  · subst r
    exact ⟨relationSyllables word_12, reduced_12, nonempty_12, length_12, nontrivial_12, evaluated_12⟩
  · subst r
    exact ⟨relationSyllables word_13, reduced_13, nonempty_13, length_13, nontrivial_13, evaluated_13⟩
  · subst r
    exact ⟨relationSyllables word_14, reduced_14, nonempty_14, length_14, nontrivial_14, evaluated_14⟩
  · subst r
    exact ⟨relationSyllables word_17, reduced_17, nonempty_17, length_17, nontrivial_17, evaluated_17⟩
  · subst r
    exact ⟨relationSyllables word_24, reduced_24, nonempty_24, length_24, nontrivial_24, evaluated_24⟩
  · subst r
    exact ⟨relationSyllables word_31, reduced_31, nonempty_31, length_31, nontrivial_31, evaluated_31⟩
  · subst r
    exact ⟨relationSyllables word_35, reduced_35, nonempty_35, length_35, nontrivial_35, evaluated_35⟩
  · subst r
    exact ⟨relationSyllables word_37, reduced_37, nonempty_37, length_37, nontrivial_37, evaluated_37⟩
  · subst r
    exact ⟨relationSyllables word_59, reduced_59, nonempty_59, length_59, nontrivial_59, evaluated_59⟩
  · subst r
    exact ⟨relationSyllables word_61, reduced_61, nonempty_61, length_61, nontrivial_61, evaluated_61⟩
  · subst r
    exact ⟨relationSyllables word_83, reduced_83, nonempty_83, length_83, nontrivial_83, evaluated_83⟩
  · subst r
    exact ⟨relationSyllables word_85, reduced_85, nonempty_85, length_85, nontrivial_85, evaluated_85⟩
  · subst r
    exact ⟨relationSyllables word_107, reduced_107, nonempty_107, length_107, nontrivial_107, evaluated_107⟩
  · subst r
    exact ⟨relationSyllables word_109, reduced_109, nonempty_109, length_109, nontrivial_109, evaluated_109⟩
  · subst r
    exact ⟨relationSyllables word_613, reduced_613, nonempty_613, length_613, nontrivial_613, evaluated_613⟩
  · subst r
    exact ⟨relationSyllables word_877, reduced_877, nonempty_877, length_877, nontrivial_877, evaluated_877⟩
  · subst r
    exact ⟨relationSyllables word_1139, reduced_1139, nonempty_1139, length_1139, nontrivial_1139, evaluated_1139⟩
  · subst r
    exact ⟨relationSyllables word_2267, reduced_2267, nonempty_2267, length_2267, nontrivial_2267, evaluated_2267⟩

#print axioms exception_certificate
#print axioms exception_hasRelation
end FiniteWords
end TwentyFour
