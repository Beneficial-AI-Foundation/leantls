import LeanBrowse.Http
import LeanBrowse.Html
/-!
# Specs: browser behaviour on concrete inputs

Former unit tests, stated as theorems. General properties are proved next to the code:
`Chunked.decode_encode`, `removeDots_no_dotdot`, `removeDots_no_dot`, and the totality of the
HTML tokenizer (structural recursion, no `partial`).

All examples here operate on `String`s, whose library functions are defined by well-founded
recursion that the kernel does not unfold, so they are checked with `native_decide`
(trusts Lean's compiler in addition to the kernel).
-/
namespace LeanBrowse.Spec
open LeanBrowse

/-! ## URLs -/

theorem parse_full :
    parseUrl "HTTPS://Example.COM:8443/a/./b/../c?x=1#frag" =
    some { scheme := "https", host := "example.com", port := 8443, path := "/a/c?x=1" } := by
  native_decide

theorem parse_bare_host :
    parseUrl "example.com" =
    some { scheme := "https", host := "example.com", port := 443, path := "/" } := by
  native_decide

theorem parse_http_query_only :
    parseUrl "http://h.org?q" = some { scheme := "http", host := "h.org", port := 80, path := "/?q" } := by
  native_decide

def base : Url := { scheme := "https", host := "x.org", port := 443, path := "/a/d/e?old" }

theorem resolve_relative :
    (resolve base "../b/c").map (·.path) = some "/a/b/c" := by native_decide

theorem resolve_sibling :
    (resolve base "f.html#top").map (·.path) = some "/a/d/f.html" := by native_decide

theorem resolve_root :
    (resolve base "/z").map (·.path) = some "/z" := by native_decide

theorem resolve_query :
    (resolve base "?new").map (·.path) = some "/a/d/e?new" := by native_decide

theorem resolve_cannot_escape_root :
    (resolve base "../../../../etc/passwd").map (·.path) = some "/etc/passwd" := by native_decide

theorem resolve_scheme_relative :
    resolve base "//cdn.y.net/lib.js" =
    some { scheme := "https", host := "cdn.y.net", port := 443, path := "/lib.js" } := by
  native_decide

theorem resolve_mailto : resolve base "mailto:a@b.c" = none := by native_decide
theorem resolve_javascript : resolve base "javascript:void(0)" = none := by native_decide

theorem resolve_absolute_http :
    resolve base "http://other.org/p" =
    some { scheme := "http", host := "other.org", port := 80, path := "/p" } := by
  native_decide

/-! ## chunked coding -/

/-- RFC-style example with a chunk extension and a trailer. -/
theorem chunked_example :
    Chunked.decode "4\r\nWiki\r\n5;ext=1\r\npedia\r\n0\r\nX-Trailer: 1\r\n\r\n".toUTF8.toList =
    some "Wikipedia".toUTF8.toList := by
  native_decide

theorem chunked_rejects_truncated :
    Chunked.decode "5\r\nab".toUTF8.toList = none := by
  native_decide

/-! ## HTTP responses -/

theorem response_chunked :
    (parseResponse ("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n" ++
      "Content-Type: text/html\r\n\r\n3\r\nabc\r\n0\r\n\r\n").toUTF8).toOption.map
      (fun r => (r.status, r.header? "content-type", r.body.toList)) =
    some (200, some "text/html", "abc".toUTF8.toList) := by
  native_decide

theorem response_content_length :
    (parseResponse "HTTP/1.1 404 Not Found\r\ncontent-length: 2\r\n\r\nhi-extra".toUTF8).toOption.map
      (fun r => (r.status, r.reason, r.body.toList)) =
    some (404, "Not Found", "hi".toUTF8.toList) := by
  native_decide

/-! ## HTML rendering -/

theorem render_basic :
    Html.render ("<!doctype html><html><head><title> Hello\n World </title>" ++
      "<style>p{color:red}</style></head><body><h1>Big &amp; bold</h1>" ++
      "<p>See <a href=\"/docs\">the docs</a> or <a href='#x'>here</a>.</p>" ++
      "<script>if (a < b) document.write('<p>no</p>')</script>" ++
      "<ul><li>one</li><li>two &lt;3</li></ul><!-- hidden --><p>caf&#233; &#x2713;</p></body></html>") =
    { title := "Hello World"
      lines := #["# Big & bold", "", "See the docs[1] or here.", "", "  • one", "  • two <3", "",
                 "café ✓"]
      links := #["/docs"] } := by
  native_decide

theorem render_pre_keeps_lines :
    (Html.render "<pre>a  b\n  c</pre>").lines = #["a  b", "  c"] := by
  native_decide

theorem render_unclosed_garbage_terminates :
    (Html.render "<<<a href=\"x\"<p <!-- never closed").links = #["x"] := by
  native_decide

theorem wrap_example :
    Html.wrap 10 "aaa bbb ccc ddd" = ["aaa bbb", "ccc ddd"] := by
  native_decide

end LeanBrowse.Spec
