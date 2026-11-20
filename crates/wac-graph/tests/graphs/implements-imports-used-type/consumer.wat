(component
  (type (instance
    (type (enum "debug" "info"))
    (export "level" (type (eq 0)))))
  (import "test:test/types" (instance $types (type 0)))
  (alias export $types "level" (type $level))
  (type (instance
    (alias outer 1 $level (type))
    (export "level" (type (eq 0)))
    (type (func (param "level" 1) (param "message" string)))
    (export "log" (func (type 2)))))
  (import "primary" (implements "test:test/logger") (instance (type 2)))
  (type (instance
    (alias outer 1 $level (type))
    (export "level" (type (eq 0)))
    (type (func (param "level" 1) (param "message" string)))
    (export "log" (func (type 2)))))
  (import "backup" (implements "test:test/logger") (instance (type 3)))
)
