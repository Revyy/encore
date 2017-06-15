all: modules

active: clean modules
	encorec active.enc

composite: clean modules
	encorec composite.enc

expr: clean modules
	encorec expr.enc

overridingFieldReqMissing: clean modules
	encorec overridingFieldReqMissing.enc

overridingPoly: clean modules
	encorec overridingPoly.enc

trait_closure: clean modules
	encorec trait_closure.enc

trait_closure_sep: clean modules
	encorec trait_closure.enc

upcast: clean modules
	encorec upcast.enc

modules: Traits_lib TraitUser_lib

Traits_lib: Traits.enc
	encorec -cl Traits.enc

TraitUser_lib: TraitUser.enc
	encorec -cl TraitUser.enc

TraitUserFail_lib: TraitUserFail.enc
	encorec -cl TraitUserFail.enc

clean:
	rm -rf active composite overridingPoly expr trait_closure Traits_lib TraitUser_lib