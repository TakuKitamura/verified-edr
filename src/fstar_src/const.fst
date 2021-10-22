module Const

open LowStar.BufferOps
open FStar.HyperStack.ST
open LowStar.Printf
open C.String

module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module B = LowStar.Buffer

noeq type struct_error = {
  code: I32.t;
  message: C.String.t;
}

noeq type fstar_uint8 = {
    value: U8.t;
    error: struct_error;
}

noeq type fstar_int32_array = {
    value: B.buffer I32.t;
    error: struct_error;
}