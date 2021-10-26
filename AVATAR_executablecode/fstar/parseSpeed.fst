module ParseSpeed

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

noeq type fstar_uint8_array = {
    value: B.buffer U8.t;
    error: struct_error;
}

val parseSpeed_body:
  can_id: U32.t ->
  can_dlc: U8.t ->
  data: B.buffer U8.t ->
  
Stack (fstar_uint8_array: fstar_uint8_array) (requires fun h0 -> 
    B.live h0 data /\
    (((B.length data) = (8)) &&
    (U32.eq can_id 0x1b4ul) &&
    (U8.eq can_dlc 5uy) &&
    (U8.gte (B.get h0 data 1) 0xD0uy) &&
    (U8.eq (B.get h0 data 2) 0uy) &&
    (U8.eq (B.get h0 data 3) 0uy) &&
    (U8.eq (B.get h0 data 4) 0uy))
  )
  (ensures fun h0 fstar_uint8_array h1 -> 
    (((I32.eq fstar_uint8_array.error.code 0l) &&
    ((B.length fstar_uint8_array.value) = (2))) ||
    (I32.eq fstar_uint8_array.error.code 1l))
  )
let parseSpeed_body can_id can_dlc data  =
    // TODO: you need to implement this function here
    push_frame();
    let ret: B.buffer U8.t = B.alloca 0uy 2ul in
    ret.(0ul) <- data.(0ul);
    ret.(1ul) <- data.(1ul);
    pop_frame ();
    {
        value = ret;
        error = {
            code = 0l;
            message = !$"";
        };
    } 

val parseSpeed: 
  can_id: U32.t ->
  can_dlc: U8.t ->
  data: B.buffer U8.t ->
  
  Stack (fstar_uint8_array: fstar_uint8_array) (requires fun h0 -> 
    B.live h0 data /\
    (((B.length data) = (8)))
  )
  (ensures fun h0 fstar_uint8_array h1 -> 
    (((I32.eq fstar_uint8_array.error.code 0l) &&
    ((B.length fstar_uint8_array.value) = (2))) ||
    (I32.eq fstar_uint8_array.error.code 1l))
  )
let parseSpeed can_id can_dlc data  = 
    // meet the preconditions
    if (let v1 = data.(1ul) in
    let v2 = data.(2ul) in
    let v3 = data.(3ul) in
    let v4 = data.(4ul) in
    ((U32.eq can_id 0x1b4ul) &&
    (U8.eq can_dlc 5uy) &&
    (U8.gte v1 0xD0uy) &&
    (U8.eq v2 0uy) &&
    (U8.eq v3 0uy) &&
    (U8.eq v4 0uy))) then
        parseSpeed_body can_id can_dlc data 
    else
        // TODO: you need to return an error value here if the preconditions are not met
        {
            value = B.null;
            error = {
            code = 1l;
                message = !$"invalid arguments";
            };
        }

