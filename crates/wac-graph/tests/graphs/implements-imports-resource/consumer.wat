(component
  (type (instance
    (export "r" (type (sub resource)))
    (export "r2" (type (eq 0)))
    (type (own 0))
    (type (borrow 1))
    (type (func (param "a" 2) (param "b" 3)))
    (export "f" (func (type 4)))))
  (import "left" (implements "test:test/res") (instance (type 0)))
  (import "right" (implements "test:test/res") (instance (type 0)))
)
