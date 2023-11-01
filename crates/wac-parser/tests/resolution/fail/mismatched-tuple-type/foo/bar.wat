(component
  (instance (import "x")
    (type $t (tuple u8 string (tuple u32)))
    (export "t" (type (eq $t)))
  )
)
