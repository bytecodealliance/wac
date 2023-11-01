(component
  (instance (import "x")
    (export "r" (type (sub resource)))
    (type $own-r (borrow 0))
    (export "f" (func (param "r" $own-r)))
  )
)
