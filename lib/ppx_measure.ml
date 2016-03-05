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

let hash = Hashtbl.create 10


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

let add_metric base_name parent callback =
  if Hashtbl.mem hash base_name
  then raise_error (
      Printf.sprintf
        "[%s] this system metric is already defined"
        base_name
    )
  else Hashtbl.add hash base_name (parent, callback)

let perform_subtypes parent =
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
                let _ = printf "add %s as a subtype\n" name in
                let _ = add_metric name parent (Some func) in
                aux xs
              | _ -> raise_error (sprintf "[%s] Malformed subtype" name)
            end
          | _ -> raise_error (sprintf "[%s] need a coersion callback" name)
          end
      | _ -> raise_error (sprintf "[%s] this subtype is malformed" name)
  in aux


let perform_type mapper item = function
  | x :: xs when List.exists
        (fun (e, _) -> e.txt = "measure") x.ptype_attributes ->
    let base_name = x.ptype_name.txt in
    let _ = printf "add %s as a type\n" base_name in
    let _ = add_metric base_name base_name None in
    let _ = perform_subtypes base_name xs in
    (wrap_in "measure-refuted" [item])
  | _ -> Ast_mapper.(default_mapper.structure_item mapper item)


let structure_item mapper item =
  match item.pstr_desc with
  | Pstr_type declarations -> perform_type mapper item declarations
  | _ -> Ast_mapper.(default_mapper.structure_item mapper item)

module Stubs =
struct

  let module_sig hash name =
    let li = [] in
    Mty.signature li

  let module_impl hash name mod_type =
    Mod.(constraint_
           (structure [])
           mod_type
        )
    |> Mb.mk (create_loc name)
    |> Str.module_

  let module_pack hash =
    module_sig hash "MEASURE"
    |> module_impl hash "Measure"

end


let structure mapper strct =
  let rec aux = function
    | x :: xs ->
      (structure_item mapper x)
      :: (aux xs)
    | _ -> []
  in
  (Stubs.module_pack hash) :: (aux strct)


let item_mapper =
  Ast_mapper.{
    default_mapper with
    structure = structure;
  }

let () =
  Ast_mapper.run_main (fun argv -> item_mapper)

