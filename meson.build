project('fizzy', 'c',
	default_options: [
		'c_std=c11',
		'warning_level=3',
	]
)

executable('fizzy',
	'fizzy.c',
	dependencies: [
		dependency('ncurses', required: true),
		dependency('readline', required: true),
	],
	install: true,
)
