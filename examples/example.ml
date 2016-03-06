[%%use_measure]

type cm [@@measure]
and  m  [@@measure fun cm -> cm *. 100.  ]
and  km [@@measure fun cm -> cm *. 1000. ]

type test
type other

type cl [@@measure]
and  dl [@@measure fun cl -> cl *. 10.   ]
and  l  [@@measure fun cl -> cl *. 100.  ]
and  kl [@@measure fun cl -> cl *. 1000. ]

type ex

let test =
  let%cm xvw = 20.0
  in xvw
let%cm x = 10.0
let%km y = 12.0
