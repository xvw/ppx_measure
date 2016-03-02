type cm [@@measure]
type m  [@@measure cm, fun x -> x *. 100.  ]
type km [@@measure cm, fun x -> x *. 1000. ]

let x = Measure.to_cm 45.
let y = Measure.to_cm 10.
let z = Measure.to_km 12.

let _ = Measure.(x + z)
