/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -verify -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -fsopt --cache_checked_modules -skip-linking -skip-compilation -no-prefix ParseSpeed -no-prefix ParseIndicator -no-prefix ParseDoor -no-prefix HardCoding parseSpeed.fst parseIndicator.fst parseDoor.fst hardCoding.fst
  F* version: <unknown>
  KreMLin version: bf7d50e8
 */

#ifndef __HardCoding_H
#define __HardCoding_H

#include "kremlib.h"




typedef struct struct_error_s
{
  int32_t code;
  C_String_t message;
}
struct_error;

int32_t __proj__Mkstruct_error__item__code(struct_error projectee);

C_String_t __proj__Mkstruct_error__item__message(struct_error projectee);


#define __HardCoding_H_DEFINED
#endif
