HTML_FILES = logo.png

all: cv.html cv.pdf cv.txt

cv.html: source.html $(HTML_FILES)
	sed 's/%%font-size%%/1em/' source.html |  sed 's/%%formats%%/<li class="formats"><a href=".\/cv.txt">plain text<\/a> \&middot; <a href=".\/cv.pdf">pdf<\/a><\/li>/' > $@

cv-nofmts.html: source.html $(HTML_FILES)
	sed 's/%%font-size%%/11pt/' source.html | sed 's/%%formats%%//' > $@

cv.txt: cv-nofmts.html plaintext.hs
	runhaskell plaintext.hs < cv-nofmts.html | sed 's/-   \[`f@mazzo\.li`\](mailto:f@mazzo\.li)/<f@mazzo.li>/' > $@

cv.pdf: cv-nofmts.html
	wkhtmltopdf -B 20 -L 25 -T 20 -R 25 cv-nofmts.html cv.pdf

clean:
	rm -f cv.html cv-nofmts.html cv.txt cv.pdf
