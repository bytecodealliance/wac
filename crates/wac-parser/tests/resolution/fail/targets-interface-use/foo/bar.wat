(component
  (type (;0;)
    (instance
      (type (;0;) (variant (case "foo")))
      (export (;1;) "my-variant" (type (eq 0)))
    )
  )
  (import "test:comp/indirect-dependency" (instance (;0;) (type 0)))
  (alias export 0 "my-variant" (type (;1;)))
  (type (;2;)
    (instance
      (alias outer 1 1 (type (;0;)))
      (export (;1;) "my-variant" (type (eq 0)))
      (type (;2;) (func (result 1)))
      (export (;0;) "fun" (func (type 2)))
    )
  )
  (import "test:comp/direct-dependency" (instance (;1;) (type 2)))
)
