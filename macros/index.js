let import = macro {
	rule { $prop:ident from $mod:lit } => {
		var $prop = require($mod);
	}
	rule { { $($prop:ident (,) ...)} from $mod:lit } => {
		var mod = require($mod);
		$(var $prop = mod.$prop;) ...
	}
}

let var = macro {
	rule { {$name:ident (,) ...} = $value } => {
		var object = $value
		$(, $name = object.$name) ...
	}
 
	rule { [$name:ident (,) ...] = $value } => {
		var array = $value, index = 0
		$(, $name = array[index++]) ...
	}
	
	rule { $name = $value } => {
		var $name = $value
	}

	rule { $name:ident } => {
		var $name
	}
}

let || = macro {
	rule infix { $left:expr | $right:expr } => {
		($left || $right)
	}

	rule infix { $left | $right } => {
		($left || $right)
	}

	rule { { $body ...} } => {
		(function () {$body ...}).bind(this)
	}
}

let | = macro {
	rule { $($arg (,) ...) | { $body ... }  } => {
		(function ($arg (,) ...) {$body ... }).bind(this)
	}
}

let @ = macro {
	rule { $name:ident } => {
		this.$name
	}
}

let fn = macro {
	rule { $name:ident ( $($arg (,) ...) ) { $body ... } } => {
		function $name ($arg (,) ...) {$body ...}
	}

	rule { ( $($arg (,) ...) ) {$body ...} } => {
		function ($arg (,) ...) {$body ...}
	}

	rule { *$name:ident ( $($arg (,) ...) ) { $body ... } } => {
		function $name *($arg (,) ...) {$body ...}
	}

	rule { *( $($arg (,) ...) ) {$body ...} } => {
		function *($arg (,) ...) {$body ...}
	}
}

let ~ = macro {
	rule { $key:ident } => {
		$key:$key
	}
}

export |;
export fn;
export ||;
export @;
export var;
export import;
export ~;
