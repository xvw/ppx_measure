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

let create_attribute value payload =
  (create_loc value, payload)

let raise_error ?(loc = !default_loc) message =
  let open Location in
  raise (Error (error ~loc message))

let wrap_in item =
  Str.attribute (
    create_attribute "measure_refuted" (PStr [item])
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
                let _ = printf "add %s as a subtype\n" name in
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
    (wrap_in item)
  | _ -> Ast_mapper.(default_mapper.structure_item mapper item)


let structure_item hash mapper item =
  match item.pstr_desc with
  | Pstr_type declarations -> perform_type hash mapper item declarations
  | _ -> Ast_mapper.(default_mapper.structure_item mapper item)

let structure hash mapper strct =
  Ast_mapper.(default_mapper.structure mapper strct)

let () =
  Ast_mapper.(register
    "ppx_measure"
    (fun argv ->
       let hash = Hashtbl.create 10 in {
         default_mapper with
         structure_item = structure_item hash;
         structure = structure hash
       }
    )
)
