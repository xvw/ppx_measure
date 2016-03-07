[%%use_measure]

type cm [@@measure]
and  m  [@@measure fun cm -> cm *. 100.  ]
and  km [@@measure fun cm -> cm *. 1000. ]


type cl [@@measure]
and  l  [@@measure fun cl -> cl *. 100.  ]
and  kl [@@measure fun cl -> cl *. 1000. ]


type euro   [@@measure]
and  dollar [@@measure fun euro -> euro /. 1.0993 ] 

let%cm a = 10.0
let%cm b = 12.0

let () =
  Printf.printf "%g : result" Measure.((a + b) |> to_float)
