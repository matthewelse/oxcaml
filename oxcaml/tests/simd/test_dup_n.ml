open Utils
open Builtins

(* Test Int8x16.dup_n *)
let () =
  let v = Int8x16.dup_n 42 in
  let low = int8x16_low_int64 v in
  let high = int8x16_high_int64 v in
  (* 42 = 0x2a repeated 8 times in each int64 *)
  let expected = 0x2a2a2a2a2a2a2a2aL in
  eq low high expected expected

(* Test Int16x8.dup_n *)
let () =
  let v = Int16x8.dup_n 1234 in
  let low = int16x8_low_int64 v in
  let high = int16x8_high_int64 v in
  (* 1234 = 0x04d2, repeated 4 times in each int64 *)
  let expected = 0x04d204d204d204d2L in
  eq low high expected expected

(* Test Int32x4.dup_n *)
let () =
  let v = Int32x4.dup_n 0x12345678l in
  let low = int32x4_low_int64 v in
  let high = int32x4_high_int64 v in
  (* 0x12345678 repeated 2 times in each int64 *)
  let expected = 0x1234567812345678L in
  eq low high expected expected

(* Test Int64x2.dup_n *)
let () =
  let v = Int64x2.dup_n 0x123456789abcdef0L in
  let low = int64x2_low_int64 v in
  let high = int64x2_high_int64 v in
  let expected = 0x123456789abcdef0L in
  eq low high expected expected

(* Test Float32x4.dup_n *)
let () =
  let open Stdlib_stable.Float32 in
  let scalar = of_float 3.14 in
  let v = Float32x4.dup_n scalar in
  let low = float32x4_low_int64 v in
  let high = float32x4_high_int64 v in
  (* The bit pattern of 3.14f repeated twice *)
  let bits = Int32.bits_of_float (to_float scalar) in
  let bits64 =
    Int64.logor (Int64.of_int32 bits)
      (Int64.shift_left (Int64.of_int32 bits) 32)
  in
  eq low high bits64 bits64

(* Test Float64x2.dup_n *)
let () =
  let scalar = 2.718 in
  let v = Float64x2.dup_n scalar in
  let low = float64x2_low_int64 v in
  let high = float64x2_high_int64 v in
  let expected = Int64.bits_of_float scalar in
  eq low high expected expected
