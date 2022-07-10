project('fizzy', 'c',
	default_options: [
		'c_std=c11',
		'warning_level=3',
	]
)

config = configuration_data()
cc = meson.get_compiler('c')
openmp_dep = dependency('openmp', required: get_option('openmp'))
config.set10('HAVE_OMP', openmp_dep.found())

executable('fizzy',
	'fizzy.c',
	configure_file(
		output: 'config.h',
		configuration: config,
	),
	dependencies: [
		dependency('readline', required: true),
		openmp_dep,
	],
	install: true,
)
