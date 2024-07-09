(component
  (type (;0;)
    (instance
      (export (;0;) "other-resource" (type (sub resource)))
    )
  )
  (import "test:comp/indirect-dependency" (instance (;0;) (type 0)))
  (alias export 0 "other-resource" (type (;1;)))
  (import "my-resource" (type (;2;) (eq 1)))
  (type (;3;) (own 2))
  (type (;4;) (func (result 3)))
  (import "my-func" (func (;0;) (type 4)))
  (alias export 0 "other-resource" (type (;5;)))
)
