krml_link = krml -verify -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -fsopt --cache_checked_modules -skip-linking -skip-compilation
no_suffix = -no-prefix ParseSpeed -no-prefix ParseIndicator -no-prefix ParseDoor -no-prefix HardCoding

all:
	$(krml_link) $(no_suffix) parseSpeed.fst parseIndicator.fst parseDoor.fst hardCoding.fst
parseSpeed:
	$(krml_link) -no-prefix ParseSpeed parseSpeed.fst
parseIndicator:
	$(krml_link) -no-prefix ParseIndicator parseIndicator.fst
parseDoor:
	$(krml_link) -no-prefix ParseDoor parseDoor.fst