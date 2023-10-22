(component
  (instance (import "x")
    (export "r" (type (sub resource)))
    (type $own-r (own 0))
    (type $borrow-r (borrow 0))
    (export "f" (func (param "r" $own-r)))
    (export "[method]r.foo" (func (param "self" $borrow-r)))
  )
)
