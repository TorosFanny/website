nHTML_FILES = logo.png

all: cv.html cv.pdf cv.txt

cv.html: source.html $(HTML_FILES)
	sed 's/%%font-size%%/1em/' source.html |  sed 's/%%formats%%/<li class="formats"><a href=".\/cv.txt">plain text<\/a> \&middot; <a href=".\/cv.pdf">pdf<\/a><\/li>/' > $@

cv-nofmts.html: source.html $(HTML_FILES)
	sed 's/%%font-size%%/11pt/' source.html | sed 's/%%formats%%//' > $@

cv.txt: cv-nofmts.html plaintext.hs
	runhaskell plaintext.hs < cv-nofmts.html > $@

cv.pdf: cv-nofmts.html
	wkhtmltopdf cv-nofmts.html cv.pdf

clean:
	rm -f cv.html cv-nofmts.html cv.txt cv.pdf
