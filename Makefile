.PHONY: check release-check certificate paper independent package
check:
	bash scripts/verify.sh twentyfour_not_free twentyfour_hasRelation twentyfour_boundedRelation twentyfour_complex_not_free twentyfour_twoStep
release-check:
	python3 scripts/check-release.py
certificate:
	python3 paper/verify_certificate.py --check
paper:
	bash paper/build.sh
independent:
	bash scripts/verify-nanoda.sh Solution twentyfour_not_free twentyfour_hasRelation twentyfour_boundedRelation twentyfour_complex_not_free twentyfour_twoStep TwentyFour.simple_direct_power_identity TwentyFour.simple_direct_scaled_certificate TwentyFour.simple_direct_four_residues_certificate
package:
	python3 scripts/make-delivery.py
