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

  let special_identity name = {
    pstr_loc = !default_loc
  ; pstr_desc = Pstr_value (Nonrecursive, [
      {
        pvb_pat = Pat.var (loc name)
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

   let typed_id name input output = {
     psig_desc = Psig_value {
         pval_name = loc name
       ; pval_type = {
           ptyp_desc = Ptyp_arrow ("", input, output)
         ; ptyp_loc = !default_loc
         ; ptyp_attributes = []
         }
       ; pval_prim = []
       ; pval_attributes = []
       ; pval_loc = !default_loc
       }
   ; psig_loc = !default_loc
   }

   let phantom (a, b) t = {
     ptyp_desc = Ptyp_constr (ident t, [a; b])
   ; ptyp_loc = !default_loc
   ; ptyp_attributes = []
   }

   let ref_type name = {
     ptyp_desc = Ptyp_constr (ident name, [])
   ; ptyp_loc = !default_loc
   ; ptyp_attributes = []
   }


  let variant_poly name = {
    ptyp_desc = Ptyp_variant (
        [Rtag (name, [], true, [])],
        Closed,
        None
      )
  ; ptyp_loc = !default_loc
  ; ptyp_attributes = []
  }

  let sig_for parent name =
    typed_id ("to_"^name) float_type (ref_type name)

   let special_identity_sig name (a, b) res =
     typed_id name (phantom (a, b) "t") res


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

  let create_type t name = {
    ptype_name = loc name
  ; ptype_params = []
  ; ptype_cstrs = []
  ; ptype_kind = Ptype_abstract
  ; ptype_private = Public
  ; ptype_manifest = t
  ; ptype_attributes = []
  ; ptype_loc = !default_loc
  }


  let precise_type (a, b) name =
    let t = {
      ptyp_desc = Ptyp_constr (ident "t", [variant_poly a; variant_poly b])
    ; ptyp_loc = !default_loc
    ; ptyp_attributes = []
    }
    in
    create_type (Some t) name


  let module_sig li name =
    {
      pmty_desc = Pmty_signature ([
          {
            psig_desc = Psig_type [(base_type None "t")]
          ; psig_loc = !default_loc
          }
        ; special_identity_sig
            "to_float"
            (subtype "base", subtype "subtype")
            float_type
        ] @ li)
    ; pmty_loc = !default_loc
    ; pmty_attributes = []
    }

  let module_binding li modtype name = {
    pmb_name = loc name
  ; pmb_expr = {
      pmod_desc =
        Pmod_constraint ({
            pmod_desc =
              Pmod_structure ([
                {
                  pstr_desc = Pstr_type [(base_type (Some float_type) "t")]
                ; pstr_loc = !default_loc
                }
                ; special_identity "to_float"
              ] @ li)
          ; pmod_loc = !default_loc
          ; pmod_attributes = []
          }, modtype)
    ; pmod_loc = !default_loc
    ; pmod_attributes = []
    }
  ; pmb_attributes = []
  ; pmb_loc = !default_loc
  }

  let create_module li typ name = {
    pstr_desc = Pstr_module (module_binding li typ name)
  ; pstr_loc = !default_loc
  }


  let is_measure (x, _) = x.txt = "measure"

  let check_type_uniq hash typ =
    let name = typ.ptype_name.txt in
    if Hashtbl.mem hash name then
      fail "Type must be uniq"
    else Hashtbl.add hash name (name, None)

end

let process_sig key parent typ payload acc =
  (Hlp.sig_for parent key)
  :: typ
  :: acc

let process_impl key parent typ payload acc =
  (Hlp.special_identity ("to_"^key))
  :: typ
  :: acc

let process_structures mapper structure =
  let hash = Hashtbl.create 10 in
  let rec aux acc  = function
    | [] -> List.rev acc
    | str :: xs ->
      let x = mapper.structure_item mapper str in
      match x.pstr_desc with
      | Pstr_type [typ] ->
        begin
          match List.filter Hlp.is_measure typ.ptype_attributes with
          | [] -> aux ([x] :: acc) xs
          | [attr, PStr [_]] ->
            let _ = Hlp.check_type_uniq hash typ in
            aux acc xs
          | [attr, PStr pl] ->
            aux acc xs
          | _ -> Hlp.fail "Malformed measure"
        end
      | _ -> aux ([x] :: acc) xs
  in
  let r = aux [] structure |> List.concat in
  let li_sig, li_impl = Hashtbl.fold (
      fun key (parent, pl) (a, b) ->
        let ax = { psig_desc = Psig_type [Hlp.create_type None key]
                 ; psig_loc = !default_loc
                 } in
        let bx = { pstr_desc = Pstr_type [Hlp.precise_type (parent, key) "cm"]
                 ; pstr_loc = !default_loc
                 } in
        (process_sig key parent ax pl a,
         process_impl key parent bx pl b)
    ) hash ([], []) in
  let ident  = Hlp.module_sig (List.rev li_sig) "MEASURE" in
  let modul = Hlp.create_module (List.rev li_impl) ident "Measure" in
  modul :: r

let new_mapper argv = {
  default_mapper with
  structure = process_structures
}

let () = register "measurement" new_mapper

