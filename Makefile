browser_info:
	cd src && isabelle build -c -d . -o browser_info -v Hygge_Theory
	mv "`isabelle getenv -b ISABELLE_BROWSER_INFO`/Unsorted/Hygge_Theory" .
	cp docs/FirstExample.png Hygge_Theory/
	rm -fr docs
	mv Hygge_Theory docs
	sed -i -e 's/Session/Library/g' docs/index.html
	sed -i -e 's/<h2>Theories<\/h2>/<h2><a href="session_graph.pdf">Index<\/a><\/h2>/g' docs/index.html
	sed -i -e 's/<p>View <a href="session_graph.pdf">theory dependencies<\/a><\/p>/<p>Denotational and operational semantics for the <a href="http:\/\/wwwdi.supelec.fr\/software\/TESL\/">Tagged Events Specification Language<\/a>.<\/p>\n<p>Check out root theory <a href="Hygge_Theory.html">Hygge_Theory<\/a> for soundness, completeness, progress and termination properties.<\/p>/g' docs/index.html
	sed -i -e 's/<\/body>/<p>Copyright (c) 2017 T. Balabonski, F. Boulanger, C. Keller, H. Nguyen Van, B. Valiron, B. Wolff, Université Paris-Sud \/ CNRS<\/p>\n<\/body>/g' docs/index.html
	sed -i -e 's/..\/..\/HOL\/HOL\//http:\/\/isabelle.in.tum.de\/website-Isabelle2017\/dist\/library\/HOL\/HOL\//g' docs/TESL.html

pdf_document:
	rm -fr src/ROOT src/document
	cd src && isabelle mkroot -d .
	sed -i -e 's/src/Hygge_Theory/g' src/ROOT
	sed -i -e 's/(\* Baz \*)/Hygge_Theory/g' src/ROOT
	sed -i -e 's/+/\n+  description {* Denotational and operational semantics for TESL *}/g' src/ROOT
	cd src && isabelle build -D .
