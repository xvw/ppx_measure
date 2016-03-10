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

open Printf
open Parsetree
open Asttypes
open Ast_helper


let create_loc ?(loc = !default_loc) value = {
  txt = value
; loc = loc
}

let ident ?(loc = !default_loc) v =
    create_loc ~loc (Longident.Lident v)

let create_attribute value payload =
  (create_loc value, payload)

let raise_error ?(loc = !default_loc) message =
  let open Location in
  raise (Error (error ~loc message))

let wrap_in name items =
  Str.attribute (
    create_attribute name (PStr items)
  )

let add_metric hash base_name parent callback =
  if Hashtbl.mem hash base_name
  then raise_error (
      Printf.sprintf
        "[%s] this system metric is already defined"
        base_name
    )
  else Hashtbl.add hash base_name (parent, callback)

let perform_subtypes hash parent =
  let rec aux = function
    | [] -> ()
    | x :: xs ->
      let name = x.ptype_name.txt in
      let attr = List.filter
          (fun (x,_) -> x.txt = "measure")
          x.ptype_attributes
      in
      match attr with
      | [_, PStr [potential_fun]] ->
        begin
          match potential_fun.pstr_desc with
          | Pstr_eval (exp, _) ->
            begin
              match exp.pexp_desc with
              | (Pexp_fun (_, _, _, _)) as func ->
                let _ = add_metric hash name parent (Some func) in
                aux xs
              | _ -> raise_error (sprintf "[%s] Malformed subtype" name)
            end
          | _ -> raise_error (sprintf "[%s] need a coersion callback" name)
          end
      | _ -> raise_error (sprintf "[%s] this subtype is malformed" name)
  in aux


let perform_type hash mapper item = function
  | x :: xs when List.exists
        (fun (e, _) -> e.txt = "measure") x.ptype_attributes ->
    let base_name = x.ptype_name.txt in
    let _ = add_metric hash base_name base_name None in
    let _ = perform_subtypes hash base_name xs in
    (wrap_in "measure-refuted" [item])
  | _ -> Ast_mapper.(default_mapper.structure_item mapper item)


module Stubs =
struct

  let type_param name = Typ.var name
  let ref_type name = Typ.constr (ident name) []
  let phantom_type (a, b) t = Typ.constr (ident t) [a; b]
  let poly name = phantom_type (type_param "base", type_param "subtype") name
  let variant name = Typ.variant [Rtag (name, [], true, [])] Closed None
  let type_of parent subtype = phantom_type (variant parent, variant subtype) "t"
  let rec arrow = function
    | [] -> raise_error "Malformed arrow type"
    | [x] -> x
    | x :: xs -> Typ.arrow "" x (arrow xs)

  let mk_type kind concrete name =
    match concrete with
    | Some x ->
      Type.mk
        ~params:([
            type_param "base", Invariant;
            type_param "subtype", Invariant;
          ])
        ~kind:kind
        ~manifest:x
        (create_loc name)
    | _ ->
      Type.mk
        ~params:([
            type_param "base", Invariant;
            type_param "subtype", Invariant;
          ])
        ~kind:kind
        (create_loc name)

  let concrete_type a b =
    Type.mk
      ~manifest:(type_of a b)
      (create_loc b)

   let base_type abstr =
    let t = if abstr then None else Some (ref_type "float") in
    mk_type Ptype_abstract t "t"

  let identity_sig name input output =
    Sig.value (Val.mk (create_loc name) (Typ.arrow "" input output))

  let identity name =
    Str.value
      Nonrecursive
      [Vb.mk
         (Pat.var (create_loc name))
         (Exp.fun_
            ""
            None
            (Pat.var (create_loc "x"))
            (Exp.ident (ident "x"))
         )]

  let alias name floatop =
    Str.value
      Nonrecursive
      [ Vb.mk (Pat.var (create_loc name)) (Exp.ident (ident floatop))]

  let alias_sig name typ =
    Sig.value (Val.mk (create_loc name) (arrow typ))

  let to_something key =
    let f = "to_"^key in
    identity f

  let to_something_sig key =
    let f = "to_"^key in
    identity_sig f (ref_type "float") (ref_type key)

  let perform_coersion_sig key parent = function
    | None -> []
    | _ ->
    let f = key^"_of_"^parent in
    [alias_sig f [ref_type parent; ref_type key]]

  let perform_coersion key parent = function
    | Some f ->
      let fname = key^"_of_"^parent in
      let v =
        Str.value
          Nonrecursive
          [Vb.mk (Pat.var (create_loc fname)) (Exp.mk f) ]
      in [v]
    | _ -> []

  let perform_hash_sig hash =
    let a, b, c = Hashtbl.fold (
      fun key (parent, func) (acc_types, acc_float, acc_coers) ->
        (
          Sig.type_ [concrete_type parent key] :: acc_types,
          to_something_sig key :: acc_float,
          (perform_coersion_sig key parent func) @ acc_coers
        )
    ) hash ([], [], [])
    in List.concat [a; b; c]


  let module_sig hash name =
    let li = [
      Sig.type_ [base_type true]
    ; identity_sig "to_float" (poly "t") (ref_type "float")
    ; alias_sig "+"          [poly "t"; poly "t"; poly "t"]
    ; alias_sig "-"          [poly "t"; poly "t"; poly "t"]
    ; alias_sig "*"          [poly "t"; ref_type "float"; poly "t"]
    ; alias_sig "/"          [poly "t"; ref_type "float"; poly "t"]
    ; alias_sig "**"         [poly "t"; ref_type "float"; poly "t"]
    ; alias_sig "ceil"       [poly "t"; poly "t"]
    ; alias_sig "floor"      [poly "t"; poly "t"]
    ; alias_sig "abs_float"  [poly "t"; poly "t"]
    ; alias_sig "mod_float"  [poly "t"; ref_type "float"; poly "t"]
    ] @ (perform_hash_sig hash)
    in Mty.signature li

    let perform_hash_impl hash =
    Hashtbl.fold (
      fun key (parent, func) acc ->
        ((Str.type_ [concrete_type parent key])
         :: to_something key :: [])
        @ (perform_coersion key parent func)
        @ acc
    ) hash []


  let module_impl hash name mod_type =
    let li = [
      Str.type_ [base_type false]
    ; identity "to_float"
    ; alias "+"           "+."
    ; alias "-"           "-."
    ; alias "*"           "*."
    ; alias "/"           "/."
    ; alias "**"          "**"
    ; alias "ceil"        "ceil"
    ; alias "floor"       "floor"
    ; alias "copysign"    "copysign"
    ; alias "abs_float"   "abs_float"
    ; alias "mod_float"   "mod_float"
    ] @ (perform_hash_impl hash)
    in Mod.(constraint_ (structure li) mod_type)
       |> Mb.mk (create_loc name)
       |> Str.module_

  let module_name = ref (Some "Measure")

  let module_pack hash name =
    module_sig hash "PPX_MEASURE_SIG"
    |> module_impl hash name

  let module_pack_with hash = function
    | PStr [] ->
      module_pack hash "Measure"
    | PStr [str] ->
      begin
        match str.pstr_desc with
        | Pstr_eval ({pexp_desc = Pexp_constant (Const_string (modname, _))}, _) ->
          let _ = module_name := Some modname in
          module_pack hash modname
        | _ -> raise_error "Malformed use_measure"
      end
    | _ -> raise_error "Malformed use_measure"

  let expr_coersion f v = {
    v with
    pvb_expr = Exp.(
        apply
          (ident (create_loc f))
          ["", v.pvb_expr]
      )
  }

  let perform_coersion name expr =
    match !module_name with
    | None -> raise_error "The measure module is not initialized"
    | Some modname ->
      begin
        match expr.pexp_desc with
        | Pexp_let (flag, vb, value) ->
          let open Longident in
          let f = Ldot (Lident modname, "to_"^name) in
          let pex = List.map (expr_coersion f) vb in
          Exp.let_ flag pex value
        | _ -> raise_error "This expression is not substituable"
      end

end


let structure hash mapper strct =
  let rec aux = function
    | x :: xs ->
      begin
        let item = Ast_mapper.(mapper.structure_item mapper x) in
        match item.pstr_desc with
        | Pstr_extension ((e, pl), _) when e.txt = "use_measure" ->
          Stubs.module_pack_with hash pl
          :: aux xs
        | Pstr_attribute (a, _) when a.txt = "measure-refuted" -> aux xs
        | _ -> item :: aux xs
      end
    | _ -> []
  in
  aux strct

let structure_item hash mapper item =
  match item.pstr_desc with
  | Pstr_type declarations -> perform_type hash mapper item declarations
  | Pstr_extension ((e, PStr [str]), _) when Hashtbl.mem hash e.txt->
    begin
      match str.pstr_desc with
      | Pstr_value (rf, vb) ->
        begin
          match !Stubs.module_name with
          | None -> raise_error "The measure module is not initialized"
          | Some modname ->
            let open Longident in
            let f = Ldot (Lident modname, "to_"^e.txt) in
            Str.value rf (List.map (Stubs.expr_coersion f) vb)
        end
      | _ -> Ast_mapper.(default_mapper.structure_item mapper item)
    end
  | _ -> Ast_mapper.(default_mapper.structure_item mapper item)

let expr hash mapper ext =
  match ext.pexp_desc with
  | Pexp_extension (e, PStr [str]) when Hashtbl.mem hash e.txt ->
    begin
      match str.pstr_desc with
      | Pstr_eval (exp, _) -> Stubs.perform_coersion e.txt exp
      | _ -> raise_error "Malformed value anotation"
    end
  | _ -> Ast_mapper.(default_mapper.expr mapper ext)


let item_mapper =
  let hash = Hashtbl.create 10 in
  Ast_mapper.{
    default_mapper with
    expr = expr hash;
    structure_item = structure_item hash;
    structure = structure hash;
  }

let () =
  Ast_mapper.run_main (fun argv -> item_mapper)

