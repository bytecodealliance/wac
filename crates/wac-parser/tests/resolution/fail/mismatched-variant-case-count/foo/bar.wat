(component
  (instance (import "x")
    (type $v (variant (case "a") (case "b" u16) (case "c" (tuple string u16))))
    (export "v" (type (eq $v)))
  )
)
