# Bounded retrieval of the Miller 2012 email

**Outcome: the email itself was not retrieved or read. Its implications for A068991 therefore remain unassessed.** This search does not establish absence of prior mathematics, novelty, or priority.

Target: Victor Miller, May 5, 2012, NMBRTHRY. The exact citation is recorded in OEIS A106741:

<https://listserv.nodak.edu/cgi-bin/wa.exe?A2=NMBRTHRY;9ede91fb.1205>

The campaign's earlier direct HTTP/HTTPS 503 failures and exact-URL Wayback empty result were read from `number_work/A068991_SOURCE_PRIOR_AUDIT.md`. The blocked cited CGI URLs were not blindly retried in this attempt. The earlier exact CDX request string was not retained; it must not be represented as a comprehensive archive search.

## New retrieval paths checked on November 27, 2026

| Path | Actual evidence | Result |
|---|---|---|
| Exact subject, message identifier, author/date, MathForum and Google Groups searches | Seventeen targeted queries across both available search engines | Found the OEIS citation, but no copy of the target message's mathematical content |
| Official NDSU service documentation | <https://kb.ndsu.edu/it/108646>, updated August 27, 2026, was opened | Still identifies `https://listserv.nodak.edu/` as the service; no replacement archive host was supplied there |
| Officially documented list-server root | <https://listserv.nodak.edu/> was opened once, as a distinct discovery route | Web retrieval reported inaccessible; no archive index or message text obtained |
| Institutional FUNET mirror | <https://ftp.funet.fi/index/files/index/Science/math/misc/mailing-lists/number-theory/> was opened and its entire listing inspected | Its newest listed monthly log is `NMBRTHRY.LOG9601` (January 1996), so this listing does not supply May 2012 |
| Possible SeqFan crosspost route | Google Groups searches and <https://list.seqfan.eu/pipermail/seqfan/2012-May/subject.html> | No target crosspost found; the old monthly index was inaccessible |
| Primary SeqFan archive-status discussion | <https://groups.google.com/g/seqfan/c/LzU7FOeGtRc>, October 14–15, 2024, was opened and read | Discusses loss/recovery of the separate SeqFan archive, not the Miller message; it does not establish that this NMBRTHRY email was present there |
| Broader Wayback month/thread lookup | Domain-wide CDX query filtered for NMBRTHRY and May-2012 code `1205`, including rewritten message URLs | The web tool could not access it; a separate read-only HTTP retrieval timed out after 30 seconds. This was a retrieval failure, **not an empty CDX result** |

The exact new Wayback request and its network outcome are saved in `wayback_monthly_result.json`; the response body file is empty because the request timed out. The query was:

```text
https://web.archive.org/cdx/search/cdx?url=listserv.nodak.edu%2F*&output=json&filter=statuscode%3A200&filter=urlkey%3A.*nmbrthry.*&filter=urlkey%3A.*1205.*&collapse=urlkey&fl=timestamp%2Coriginal%2Cstatuscode%2Cdigest&limit=50
```

## Assessment boundary

The known citation concerns the related Bernoulli-denominator sequence A106741. That bibliographic context alone does not reveal what Miller proved. In particular, no inference was made about whether his message proves the complete A068991 implication from squarefreeness and an integral divisor sum to divisibility of the Bernoulli denominator.

The email remains an explicit unread-reference limitation. The existing A068991 kernel verification is a separate fact and was not rerun or changed. This task made no claim, PR, main-branch, lease, or schedule changes and sent no external correspondence.

Report by ChatGPT/Codex (GPT-6; exact serving variant not exposed), assisting Cornelius Lytollis (@con123-gif).
