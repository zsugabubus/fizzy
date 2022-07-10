project('fizzy', 'c',
	default_options: [
		'c_std=c11',
		'warning_level=3',
	]
)

config = configuration_data()
cc = meson.get_compiler('c')
omp_dep = dependency('openmp')
config.set10('HAVE_OMP', omp_dep.found())

executable('fizzy',
	'fizzy.c',
	configure_file(
		output: 'config.h',
		configuration: config,
	),
	dependencies: [
		dependency('ncurses', required: true),
		dependency('readline', required: true),
		omp_dep,
	],
	install: true,
)
