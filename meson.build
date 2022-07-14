project('fizzy', 'c',
	default_options: [
		'c_std=c11',
		'warning_level=3',
	]
)

config = configuration_data()
cc = meson.get_compiler('c')
openmp_dep = dependency('openmp', required: get_option('openmp'))
if not cc.has_function('__builtin_clz')
	error()
endif
config.set10('WITH_OMP', openmp_dep.found())

fizzy = executable('fizzy',
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

pod2man = find_program('pod2man')

custom_target(
	'man',
	output: meson.project_name() + '.1',
	input: 'README.pod',
	command: [
		pod2man,
		'--section=1',
		'--center=Fuzzy searcher',
		'--name=' + meson.project_name(),
		'--release=@1@ @0@'.format(
			meson.project_name(),
			meson.project_version(),
		),
		'@INPUT@', '@OUTPUT@'
	],
	install: true,
	install_dir: get_option('mandir') / 'man1'
)

test('functional tests', find_program('check'))
