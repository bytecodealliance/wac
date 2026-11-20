(component
  (type (instance
    (type (enum "debug" "info"))
    (export "level" (type (eq 0)))
    (type (func (param "level" 1) (param "message" string)))
    (export "log" (func (type 2)))))
  (import "primary" (implements "test:test/logger") (instance (type 0)))
  (type (instance
    (type (enum "debug" "info"))
    (export "level" (type (eq 0)))
    (type (func (param "level" 1) (param "message" string)))
    (export "log" (func (type 2)))))
  (import "backup" (implements "test:test/logger") (instance (type 1)))
)
