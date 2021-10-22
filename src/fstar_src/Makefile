krml_link = krml -verify -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -fsopt --cache_checked_modules -skip-linking -skip-compilation -no-prefix

all: parseSpeed parseIndicator parseDoor
parseSpeed:
	$(krml_link) ParseSpeed parseSpeed.fst
parseIndicator:
	$(krml_link) ParseIndicator parseIndicator.fst
parseDoor:
	$(krml_link) ParseDoor parseDoor.fst