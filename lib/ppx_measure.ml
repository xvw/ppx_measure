(*
 * ppx_measure is a general purposition to add unit of measure in OCaml
 *
 * Copyright (c) 2015 Xavier Van de Woestyne <xaviervdw@gmail.com>
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 *)

open Ast_mapper
open Ast_helper
open Asttypes
open Parsetree
open Longident

(* Helpers with presaved "components" *)
module Hlp =
struct

  let fail ?(loc = !default_loc) message =
    let open Location in
    raise (Error (error ~loc message))

  let create_loc ?(loc = !default_loc) value = {
    txt = value
  ; loc = loc
  }
  let loc = create_loc

  let ident ?(loc = !default_loc) v =
    create_loc ~loc (Lident v)

  let float_type = {
      ptyp_desc = Ptyp_constr (ident "float", [])
    ; ptyp_loc = !default_loc
    ; ptyp_attributes = []
    }

  let subtype name = {
    ptyp_desc = Ptyp_var name
  ; ptyp_loc = !default_loc
  ; ptyp_attributes = []
  }

  let fun_to_float = {
    pstr_loc = !default_loc
  ; pstr_desc = Pstr_value (Nonrecursive, [
      {
        pvb_pat = Pat.var (loc "to_float")
      ; pvb_expr =
          Exp.fun_
            ""
            None
            (Pat.var (loc "x"))
            (Exp.ident (ident "x"))
      ; pvb_attributes = []
      ; pvb_loc = !default_loc
      }
    ])
  }

  let fun_to_float_sig = {
    psig_desc = Psig_value {
        pval_name = loc "to_float"
      ; pval_type = {
          ptyp_desc = Ptyp_arrow (
              "",
              {
                ptyp_desc =
                  Ptyp_constr (ident "t",[subtype "base"; subtype "subtype"])
              ; ptyp_loc = !default_loc
              ; ptyp_attributes = []
              },
              float_type
            )
        ; ptyp_loc = !default_loc
        ; ptyp_attributes = []
        }
      ; pval_prim = []
      ; pval_attributes = []
      ; pval_loc = !default_loc
      }
  ; psig_loc = !default_loc
  }

  let base_type concrete_type name = {
    ptype_name = loc name
  ; ptype_params = [
      (subtype "base", Invariant);
      (subtype "subtype", Invariant)
    ]
  ; ptype_cstrs = []
  ; ptype_kind = Ptype_abstract
  ; ptype_private = Public
  ; ptype_manifest = concrete_type
  ; ptype_attributes = []
  ; ptype_loc = !default_loc
  }


  let module_sig name =
    {
      pmty_desc = Pmty_signature [
          {
            psig_desc = Psig_type [(base_type None "t")]
          ; psig_loc = !default_loc
          }
          ; fun_to_float_sig
        ]
    ; pmty_loc = !default_loc
    ; pmty_attributes = []
    }

  let module_binding modtype name = {
    pmb_name = loc name
  ; pmb_expr = {
      pmod_desc =
        Pmod_constraint ({
            pmod_desc =
              Pmod_structure [
                {
                  pstr_desc = Pstr_type [(base_type (Some float_type) "t")]
                ; pstr_loc = !default_loc
                }
                ; fun_to_float
              ]
          ; pmod_loc = !default_loc
          ; pmod_attributes = []
          }, modtype)
    ; pmod_loc = !default_loc
    ; pmod_attributes = []
    }
  ; pmb_attributes = []
  ; pmb_loc = !default_loc
  }

  let create_module typ name = {
    pstr_desc = Pstr_module (module_binding typ name)
  ; pstr_loc = !default_loc
  }

end

let process_structures mapper structure =
  let rec aux acc  = function
    | [] -> List.rev acc
    | str :: xs ->
      let x = mapper.structure_item mapper str in
      aux ([x] :: acc) xs
  in
  let r = aux [] structure |> List.concat in
  let ident  = Hlp.module_sig "MEASURE" in
  let modul = Hlp.create_module ident "Measure" in
  modul :: r

let new_mapper argv = {
  default_mapper with
  structure = process_structures
}

let () = register "measurement" new_mapper

