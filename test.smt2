(declare-fun f (Int) Bool)
(assert (f 13))
(assert (not (f 12)))
(check-sat)
(get-model)
