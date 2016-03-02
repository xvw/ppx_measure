type cm [@@measure]
type m  [@@measure cm, fun x -> x *. 100.  ]
type km [@@measure cm, fun x -> x *. 1000. ]

let%cm x = 45.
let y = Measure.to_cm 10.
let%km = 10.

let _ = Measure.(x + z)

